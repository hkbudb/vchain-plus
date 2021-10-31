use anyhow::{bail, Context, Result};
use rand::{seq::SliceRandom, Rng};
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::{
    collections::{BTreeMap, HashSet},
    fs::{self, File},
    iter::FromIterator,
    path::PathBuf,
};
use structopt::StructOpt;
use tracing::debug;
use vchain_plus::{
    chain::{
        block::Height,
        query::query_param::{AndNode, Node, NotNode, OrNode, QueryParam},
        range::Range,
        traits::ScanQueryInterface,
    },
    digest::Digest,
    utils::init_tracing_subscriber,
    SimChain,
};

const QUERY_NUM: usize = 5;
const ERR_RATE: f64 = 0.1;
const START_COEFFICIENT: u32 = 1000000;

#[allow(clippy::too_many_arguments)]
fn gen_range_query<T: ScanQueryInterface<K = u32>>(
    time_win: u32,
    selectivity: f64,
    err_rate: f64,
    dim_num: usize,
    chain: T,
    obj_num: u32,
    blk_num: u32,
    gaps: &[u32],
) -> Result<(String, String)> {
    let mut rng = rand::thread_rng();
    let mut start_blk_height;
    let mut end_blk_height;
    loop {
        start_blk_height = Height(rng.gen_range(1..blk_num));
        end_blk_height = Height(start_blk_height.0 + time_win - 1);
        if end_blk_height.0 <= blk_num {
            break;
        }
    }
    debug!(
        "start_blk: {}, end_blk: {}",
        start_blk_height, end_blk_height
    );
    let num_scopes = chain.get_range_info(start_blk_height, end_blk_height, dim_num)?;
    debug!("num scpoes: {:?}", num_scopes);
    let obj_num_per_blk = obj_num / blk_num;
    let obj_num_in_query_win = (time_win as f64 * obj_num_per_blk as f64) as u32;
    let dim_selectivity = selectivity;
    debug!("dim_selec: {}", dim_selectivity);
    let sub_selectivity = dim_selectivity.powf(1_f64 / dim_num as f64);
    debug!("sub_selec: {}", sub_selectivity);
    let mut sub_results = Vec::<(usize, Range<u32>, usize, HashSet<Digest>)>::new();
    let mut cur_res_set = HashSet::<Digest>::new();
    let mut flag = true;
    for (dim, range) in num_scopes.iter().enumerate() {
        let selected_len = (time_win as f64 * obj_num_per_blk as f64 * sub_selectivity) as u32;
        debug!("selected_len for dim {} is: {}", dim, selected_len);
        let mut start_p;
        let mut end_p;
        let mut counter = 0;
        loop {
            let l = range.get_low();
            let h = range.get_high();
            start_p = rng.gen_range(l..(l + h / START_COEFFICIENT + 1));
            end_p = start_p + selected_len;
            if end_p <= range.get_high() {
                break;
            }
            counter += 1;
            if counter >= 500 {
                break;
            }
        }
        let sub_range = Range::new(start_p, end_p);
        let sub_res = chain.range_query(sub_range, start_blk_height, end_blk_height, dim)?;
        if flag {
            cur_res_set = sub_res.clone();
            flag = false;
        } else {
            cur_res_set = cur_res_set.intersection(&sub_res).cloned().collect();
        }
        sub_results.push((sub_res.len(), sub_range, dim, sub_res));
    }
    debug!("sub_res: {:?}", sub_results);
    debug!("cur_res_set len: {}", cur_res_set.len());

    while cur_res_set.len()
        < (obj_num_in_query_win as f64 * (selectivity * (1_f64 - err_rate))) as usize
        || cur_res_set.len()
            > (obj_num_in_query_win as f64 * (selectivity * (1_f64 + err_rate))) as usize
    {
        sub_results.sort_by(|a, b| a.0.cmp(&b.0));
        flag = true;
        let new_sub_range;
        let modified_dim;
        if cur_res_set.len()
            < (obj_num_in_query_win as f64 * (selectivity * (1_f64 - err_rate))) as usize
        {
            debug!("less than target");
            let (_, sub_range, dim, _) = sub_results.remove(0);
            let l = sub_range.get_low();
            let h = sub_range.get_high();
            if h + gaps.get(dim).context("gap not exist")?
                < num_scopes
                    .get(dim)
                    .context("Range does not exist")?
                    .get_high()
            {
                new_sub_range = Range::new(l, h + gaps.get(dim).context("gap not exist")?);
            } else {
                new_sub_range = Range::new(l - gaps.get(dim).context("gap not exist")?, h);
            }
            modified_dim = dim;
        } else {
            debug!("more than target");
            let sub_res_len = sub_results.len();
            let (_, sub_range, dim, _) = sub_results.remove(sub_res_len - 1);

            let l = sub_range.get_low();
            let h = sub_range.get_high();
            if h > l + gaps.get(dim).context("gap not exist")? {
                new_sub_range = Range::new(l, h - gaps.get(dim).context("gap not exist")?);
            } else {
                bail!("Cannot reduce the range anymore");
            }
            modified_dim = dim;
        }
        let new_sub_res = chain.range_query(
            new_sub_range,
            start_blk_height,
            end_blk_height,
            modified_dim,
        )?;
        sub_results.push((new_sub_res.len(), new_sub_range, modified_dim, new_sub_res));

        debug!(
            "start_blk: {}, end_blk: {}",
            start_blk_height, end_blk_height
        );
        debug!("ranges:");
        for (_, sub_range, _, sub_res) in &sub_results {
            if flag {
                cur_res_set = sub_res.clone();
                flag = false;
            } else {
                cur_res_set = cur_res_set.intersection(sub_res).cloned().collect();
            }
            debug!("{:?}", sub_range);
        }
        debug!("cur_res_set_len: {}", cur_res_set.len());
    }

    let mut ranges = BTreeMap::<usize, Range<u32>>::new();
    for (_, r, dim, _) in sub_results {
        ranges.insert(dim, r);
    }

    let mut vchain_plus_range = Vec::<Vec<u32>>::new();
    let mut vchain_range = Vec::<Vec<u32>>::new();
    let mut vchain_range_start = Vec::<u32>::new();
    let mut vchain_range_end = Vec::<u32>::new();
    for (_, range) in ranges {
        let l = range.get_low();
        let r = range.get_high();
        vchain_plus_range.push(vec![l, r]);
        vchain_range_start.push(l);
        vchain_range_end.push(r);
    }
    vchain_range.push(vchain_range_start);
    vchain_range.push(vchain_range_end);

    let vchain_plus_query_param_json = json!({
        "start_blk": start_blk_height.0,
        "end_blk": end_blk_height.0,
        "range": vchain_plus_range,
        "keyword_exp": null,
    });
    let vchain_plus_query_param = serde_json::to_string_pretty(&vchain_plus_query_param_json)?;

    let vchain_query_param_json = json!({
        "start_block": start_blk_height.0,
        "end_block": end_blk_height.0,
        "range": vchain_range,
        "bool": null,
    });

    let vchain_query_param = serde_json::to_string_pretty(&vchain_query_param_json)?;

    Ok((vchain_plus_query_param, vchain_query_param))
}

fn get_exp_str(node: &Node) -> HashSet<&String> {
    let mut res = HashSet::<&String>::new();
    match node {
        Node::And(n) => {
            let AndNode(c1, c2) = n.as_ref();
            let res1 = get_exp_str(c1);
            let res2 = get_exp_str(c2);
            let sub_res: HashSet<&String> = res1.union(&res2).cloned().collect();
            res = res.union(&sub_res).cloned().collect();
        }
        Node::Or(n) => {
            let OrNode(c1, c2) = n.as_ref();
            let res1 = get_exp_str(c1);
            let res2 = get_exp_str(c2);
            let sub_res: HashSet<&String> = res1.union(&res2).cloned().collect();
            res = res.union(&sub_res).cloned().collect();
        }
        Node::Not(_) => {}
        Node::Input(n) => {
            res.insert(n);
        }
    }
    res
}

fn gen_node_with_not(not_prob: f64, keyword: String) -> Node {
    let mut rng = rand::thread_rng();
    let y: f64 = rng.gen();
    if y > not_prob {
        Node::Input(keyword)
    } else {
        Node::Not(Box::new(NotNode(Node::Input(keyword))))
    }
}

fn gen_keyword_query<T: ScanQueryInterface<K = u32>>(
    time_win: u32,
    with_not: bool,
    not_prob: f64,
    keyword_num: usize,
    blk_num: u32,
    chain: T,
    fix_pattern: u8,
) -> Result<(String, String)> {
    let mut rng = rand::thread_rng();
    let mut start_blk_height_num;
    let mut end_blk_height_num;
    loop {
        start_blk_height_num = rng.gen_range(1..blk_num);
        end_blk_height_num = start_blk_height_num + time_win - 1;
        if end_blk_height_num <= blk_num {
            break;
        }
    }
    let keyword_domain =
        chain.get_keyword_info(Height(start_blk_height_num), Height(end_blk_height_num))?;
    let keyword_vec = Vec::from_iter(keyword_domain);
    let keywords_selected: HashSet<&String> =
        HashSet::from_iter(keyword_vec.choose_multiple(&mut rand::thread_rng(), keyword_num));

    let mut node: Node = Node::Input("init".to_string());
    if fix_pattern == 3 {
        let mut and_flag = true;
        let mut v_1 = Vec::<Node>::new();
        let mut v_2 = Vec::<Node>::new();
        for keyword in keywords_selected {
            v_1.push(Node::Input(keyword.to_string()));
        }
        if v_1.len() == 1 {
            node = v_1.get(0).cloned().context("v_1 is empty")?;
        } else {
            while v_1.len() > 1 {
                loop {
                    if v_1.len() == 1 {
                        bail!("odd keyword num");
                    } else if v_1.is_empty() {
                        break;
                    }
                    let n_1 = v_1.pop();
                    let n_2 = v_1.pop();
                    let new_n = if and_flag {
                        Node::And(Box::new(AndNode(
                            n_1.context("n_1 is none")?,
                            n_2.context("n_2 is none")?,
                        )))
                    } else {
                        Node::Or(Box::new(OrNode(
                            n_1.context("n_1 is none")?,
                            n_2.context("n_2 is none")?,
                        )))
                    };
                    v_2.push(new_n);
                }
                and_flag = false;
                v_1.append(&mut v_2);
            }
            node = v_1.pop().context("root is none")?;
        }
    } else {
        let mut lock = false;
        for keyword in keywords_selected {
            if lock {
                if fix_pattern == 0 {
                    let idx = rng.gen_range(0..2); // 0: and, 1: or
                    if idx == 0 {
                        if with_not {
                            node = Node::And(Box::new(AndNode(
                                node,
                                gen_node_with_not(not_prob, keyword.to_string()),
                            )));
                        } else {
                            node = Node::And(Box::new(AndNode(
                                node,
                                Node::Input(keyword.to_string()),
                            )));
                        }
                    } else if with_not {
                        node = Node::Or(Box::new(OrNode(
                            node,
                            gen_node_with_not(not_prob, keyword.to_string()),
                        )));
                    } else {
                        node = Node::Or(Box::new(OrNode(node, Node::Input(keyword.to_string()))));
                    }
                } else if fix_pattern == 1 {
                    node = Node::And(Box::new(AndNode(node, Node::Input(keyword.to_string()))));
                } else if fix_pattern == 2 {
                    node = Node::Or(Box::new(OrNode(node, Node::Input(keyword.to_string()))));
                }
            } else {
                if fix_pattern == 0 {
                    if with_not {
                        node = gen_node_with_not(not_prob, keyword.to_string())
                    } else {
                        node = Node::Input(keyword.to_string());
                    }
                } else {
                    node = Node::Input(keyword.to_string());
                }
                lock = true;
            }
        }
    }

    let cnf_set = node.to_cnf_set();

    let query_param = QueryParam {
        start_blk: start_blk_height_num,
        end_blk: end_blk_height_num,
        range: Vec::<Range<u32>>::new(),
        keyword_exp: Some(node),
    };
    let vchain_plus_query_param = serde_json::to_string_pretty(&query_param)?;

    let mut total_bool = vec![];
    for n in &cnf_set {
        let arr: Vec<String> = get_exp_str(n).into_iter().cloned().collect();
        total_bool.push(arr);
    }
    let vchain_query_param_json = json!({
        "start_block": start_blk_height_num,
        "end_block": end_blk_height_num,
        "range": null,
        "bool": total_bool,
    });

    let vchain_query_param = serde_json::to_string_pretty(&vchain_query_param_json)?;

    Ok((vchain_plus_query_param, vchain_query_param))
}

#[allow(clippy::too_many_arguments)]
fn gen_keyword_range_query<T: ScanQueryInterface<K = u32>>(
    time_win: u32,
    selectivity: f64,
    err_rate: f64,
    dim_num: usize,
    chain: T,
    obj_num: u32,
    blk_num: u32,
    with_not: bool,
    not_prob: f64,
    keyword_num: usize,
    fix_pattern: u8,
    gaps: &[u32],
) -> Result<(String, String)> {
    let mut rng = rand::thread_rng();
    let mut start_blk_height;
    let mut end_blk_height;
    loop {
        start_blk_height = Height(rng.gen_range(1..blk_num));
        end_blk_height = Height(start_blk_height.0 + time_win - 1);
        if end_blk_height.0 <= blk_num {
            break;
        }
    }

    // for range query
    let num_scopes = chain.get_range_info(start_blk_height, end_blk_height, dim_num)?;
    let obj_num_per_blk = obj_num / blk_num;
    let obj_num_in_query_win = (time_win as f64 * obj_num_per_blk as f64) as u32;
    let dim_selectivity = selectivity;
    let sub_selectivity = dim_selectivity.powf(1_f64 / dim_num as f64);
    let mut sub_results = Vec::<(usize, Range<u32>, usize, HashSet<Digest>)>::new();
    let mut cur_res_set = HashSet::<Digest>::new();
    let mut flag = true;
    for (dim, range) in num_scopes.iter().enumerate() {
        let selected_len = (time_win as f64 * obj_num_per_blk as f64 * sub_selectivity) as u32;
        let mut start_p;
        let mut end_p;
        let mut counter = 0;
        loop {
            let l = range.get_low();
            let h = range.get_high();
            start_p = rng.gen_range(l..(l + h / START_COEFFICIENT + 1));
            end_p = start_p + selected_len;
            if end_p <= range.get_high() {
                break;
            }
            counter += 1;
            if counter >= 500 {
                break;
            }
        }
        let sub_range = Range::new(start_p, end_p);
        let sub_res = chain.range_query(sub_range, start_blk_height, end_blk_height, dim)?;
        if flag {
            cur_res_set = sub_res.clone();
            flag = false;
        } else {
            cur_res_set = cur_res_set.intersection(&sub_res).cloned().collect();
        }
        sub_results.push((sub_res.len(), sub_range, dim, sub_res));
    }

    while cur_res_set.len()
        < (obj_num_in_query_win as f64 * (selectivity * (1_f64 - err_rate))) as usize
        || cur_res_set.len()
            > (obj_num_in_query_win as f64 * (selectivity * (1_f64 + err_rate))) as usize
    {
        sub_results.sort_by(|a, b| a.0.cmp(&b.0));
        flag = true;
        let new_sub_range;
        let modified_dim;
        if cur_res_set.len()
            < (obj_num_in_query_win as f64 * (selectivity * (1_f64 - err_rate))) as usize
        {
            let (_, sub_range, dim, _) = sub_results.remove(0);
            let l = sub_range.get_low();
            let h = sub_range.get_high();
            if h + gaps.get(dim).context("gap not exist")?
                < num_scopes
                    .get(dim)
                    .context("Range does not exist")?
                    .get_high()
            {
                new_sub_range = Range::new(l, h + gaps.get(dim).context("gap not exist")?);
            } else {
                new_sub_range = Range::new(l - gaps.get(dim).context("gap not exist")?, h);
            }
            modified_dim = dim;
        } else {
            let sub_res_len = sub_results.len();
            let (_, sub_range, dim, _) = sub_results.remove(sub_res_len - 1);

            let l = sub_range.get_low();
            let h = sub_range.get_high();
            if h > l + gaps.get(dim).context("gap not exist")? {
                new_sub_range = Range::new(l, h - gaps.get(dim).context("gap not exist")?);
            } else {
                bail!("Cannot reduce the range anymore");
            }
            modified_dim = dim;
        }
        let new_sub_res = chain.range_query(
            new_sub_range,
            start_blk_height,
            end_blk_height,
            modified_dim,
        )?;
        sub_results.push((new_sub_res.len(), new_sub_range, modified_dim, new_sub_res));

        for (_, _sub_range, _, sub_res) in &sub_results {
            if flag {
                cur_res_set = sub_res.clone();
                flag = false;
            } else {
                cur_res_set = cur_res_set.intersection(sub_res).cloned().collect();
            }
        }
        debug!("cur_res_set_len: {}", cur_res_set.len());
    }

    let mut ranges = BTreeMap::<usize, Range<u32>>::new();
    for (_, r, dim, _) in sub_results {
        ranges.insert(dim, r);
    }

    let mut vchain_plus_range = Vec::<Range<u32>>::new();
    let mut vchain_range = Vec::<Vec<u32>>::new();
    let mut vchain_range_start = Vec::<u32>::new();
    let mut vchain_range_end = Vec::<u32>::new();
    for (_, range) in ranges {
        let l = range.get_low();
        let r = range.get_high();
        vchain_plus_range.push(Range::new(l, r));
        vchain_range_start.push(l);
        vchain_range_end.push(r);
    }
    vchain_range.push(vchain_range_start);
    vchain_range.push(vchain_range_end);

    // for keyword query
    let keyword_domain = chain.get_keyword_info(start_blk_height, end_blk_height)?;
    let keyword_vec = Vec::from_iter(keyword_domain);
    let keywords_selected: Vec<&String> = keyword_vec
        .choose_multiple(&mut rand::thread_rng(), keyword_num)
        .collect();

    let mut node: Node = Node::Input("init".to_string());
    if fix_pattern == 3 {
        let mut and_flag = true;
        let mut v_1 = Vec::<Node>::new();
        let mut v_2 = Vec::<Node>::new();
        for keyword in keywords_selected {
            v_1.push(Node::Input(keyword.to_string()));
        }
        if v_1.len() == 1 {
            node = v_1.get(0).cloned().context("v_1 is empty")?;
        } else {
            while v_1.len() > 1 {
                loop {
                    if v_1.len() == 1 {
                        bail!("odd keyword num");
                    } else if v_1.is_empty() {
                        break;
                    }
                    let n_1 = v_1.pop();
                    let n_2 = v_1.pop();
                    let new_n = if and_flag {
                        Node::And(Box::new(AndNode(
                            n_1.context("n_1 is none")?,
                            n_2.context("n_2 is none")?,
                        )))
                    } else {
                        Node::Or(Box::new(OrNode(
                            n_1.context("n_1 is none")?,
                            n_2.context("n_2 is none")?,
                        )))
                    };
                    v_2.push(new_n);
                }
                and_flag = false;
                v_1.append(&mut v_2);
            }
            node = v_1.pop().context("root is none")?;
        }
    } else {
        let mut lock = false;
        for keyword in keywords_selected {
            if lock {
                if fix_pattern == 0 {
                    let idx = rng.gen_range(0..2); // 0: and, 1: or
                    if idx == 0 {
                        if with_not {
                            node = Node::And(Box::new(AndNode(
                                node,
                                gen_node_with_not(not_prob, keyword.to_string()),
                            )));
                        } else {
                            node = Node::And(Box::new(AndNode(
                                node,
                                Node::Input(keyword.to_string()),
                            )));
                        }
                    } else if with_not {
                        node = Node::Or(Box::new(OrNode(
                            node,
                            gen_node_with_not(not_prob, keyword.to_string()),
                        )));
                    } else {
                        node = Node::Or(Box::new(OrNode(node, Node::Input(keyword.to_string()))));
                    }
                } else if fix_pattern == 1 {
                    node = Node::And(Box::new(AndNode(node, Node::Input(keyword.to_string()))));
                } else if fix_pattern == 2 {
                    node = Node::Or(Box::new(OrNode(node, Node::Input(keyword.to_string()))));
                }
            } else {
                if fix_pattern == 0 {
                    if with_not {
                        node = gen_node_with_not(not_prob, keyword.to_string())
                    } else {
                        node = Node::Input(keyword.to_string());
                    }
                } else {
                    node = Node::Input(keyword.to_string());
                }
                lock = true;
            }
        }
    }

    let cnf_set = node.to_cnf_set();
    let query_param = QueryParam {
        start_blk: start_blk_height.0,
        end_blk: end_blk_height.0,
        range: vchain_plus_range,
        keyword_exp: Some(node),
    };
    let vchain_plus_query_param = serde_json::to_string_pretty(&query_param)?;
    let mut total_bool = vec![];
    for n in &cnf_set {
        let arr: Vec<String> = get_exp_str(n).into_iter().cloned().collect();
        total_bool.push(arr);
    }
    let vchain_query_param_json = json!({
        "start_block": start_blk_height.0,
        "end_block": end_blk_height.0,
        "range": vchain_range,
        "bool": total_bool,
    });
    let vchain_query_param = serde_json::to_string_pretty(&vchain_query_param_json)?;
    Ok((vchain_plus_query_param, vchain_query_param))
}

#[derive(StructOpt, Debug)]
struct Opt {
    /// range query only
    #[structopt(short, long)]
    range: bool,

    /// keyword query only
    #[structopt(short, long)]
    keyword: bool,

    // keyword range query
    #[structopt(short, long)]
    both: bool,

    /// has not
    #[structopt(short, long)]
    with_not: bool,

    /// fix keyword query pattern
    /// 0: No pattern
    /// 1: AND
    /// 2: OR
    /// 3: tx-based pattern
    #[structopt(short, long)]
    fix_pattern: u8,

    /// probability of not opt
    #[structopt(short, long, default_value = "0.0")]
    prob_not: f64,

    /// query time window size
    #[structopt(short, long)]
    time_win: u32,

    /// dim number
    #[structopt(short, long, default_value = "1")]
    dim_num: usize,

    /// gap
    #[structopt(short, long, default_value = "1000")]
    gaps: Vec<u32>,

    /// selectivity for range query
    #[structopt(short, long)]
    selectivity: f64,

    /// keyword number
    #[structopt(short, long, default_value = "0")]
    num_keywords: usize,

    /// input db path, should be a directory
    #[structopt(short, long, parse(from_os_str))]
    input: PathBuf,

    /// output path, should be a directory
    #[structopt(short, long, parse(from_os_str))]
    output: PathBuf,
}

#[derive(Debug, Default, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct VChainQuery {
    pub start_block: u32,
    pub end_block: u32,
    pub range: Option<Vec<Vec<u32>>>,
    pub bool: Option<Vec<HashSet<String>>>,
}

fn main() -> Result<()> {
    init_tracing_subscriber("debug")?;
    let opts = Opt::from_args();
    let output_path = opts.output;
    fs::create_dir_all(&output_path)?;
    let chain = SimChain::open(&opts.input)?;
    let time_win = opts.time_win;
    let mut query_for_plus = Vec::<QueryParam<u32>>::new();
    let mut query_for_vchain = Vec::<VChainQuery>::new();

    let plus_buffer = output_path.join("plus_buffer.json");
    let chain_buffer = output_path.join("vchain_buffer.json");

    for _ in 0..QUERY_NUM {
        let mut plus_params: Vec<QueryParam<u32>>;
        let mut chain_params: Vec<VChainQuery>;
        if plus_buffer.exists() {
            let plus_data = fs::read_to_string(plus_buffer.clone())?;
            plus_params = serde_json::from_str(&plus_data)?;
        } else {
            File::create(plus_buffer.clone())?;
            plus_params = Vec::new();
        }
        if chain_buffer.exists() {
            let chain_data = fs::read_to_string(chain_buffer.clone())?;
            chain_params = serde_json::from_str(&chain_data)?;
        } else {
            File::create(chain_buffer.clone())?;
            chain_params = Vec::new();
        }

        if opts.range {
            let (obj_num, blk_num) = (&chain).get_chain_info()?;
            let (q_for_plus, q_for_vchain) = gen_range_query(
                time_win,
                opts.selectivity,
                ERR_RATE,
                opts.dim_num,
                &chain,
                obj_num,
                blk_num,
                &opts.gaps,
            )?;
            let query_param_plus: QueryParam<u32> = serde_json::from_str(&q_for_plus)?;
            plus_params.push(query_param_plus.clone());
            query_for_plus.push(query_param_plus);
            let query_vchain: VChainQuery = serde_json::from_str(&q_for_vchain)?;
            chain_params.push(query_vchain.clone());
            query_for_vchain.push(query_vchain);
        } else if opts.keyword {
            let (_obj_num, blk_num) = (&chain).get_chain_info()?;
            let (q_for_plus, q_for_vchain) = gen_keyword_query(
                time_win,
                opts.with_not,
                opts.prob_not,
                opts.num_keywords,
                blk_num,
                &chain,
                opts.fix_pattern,
            )?;
            let query_param_plus: QueryParam<u32> = serde_json::from_str(&q_for_plus)?;
            plus_params.push(query_param_plus.clone());
            query_for_plus.push(query_param_plus);
            let query_vchain: VChainQuery = serde_json::from_str(&q_for_vchain)?;
            chain_params.push(query_vchain.clone());
            query_for_vchain.push(query_vchain);
        } else if opts.both {
            let (obj_num, blk_num) = (&chain).get_chain_info()?;
            let (q_for_plus, q_for_vchain) = gen_keyword_range_query(
                time_win,
                opts.selectivity,
                ERR_RATE,
                opts.dim_num,
                &chain,
                obj_num,
                blk_num,
                opts.with_not,
                opts.prob_not,
                opts.num_keywords,
                opts.fix_pattern,
                &opts.gaps,
            )?;
            let query_param_plus: QueryParam<u32> = serde_json::from_str(&q_for_plus)?;
            plus_params.push(query_param_plus.clone());
            query_for_plus.push(query_param_plus);
            let query_vchain: VChainQuery = serde_json::from_str(&q_for_vchain)?;
            chain_params.push(query_vchain.clone());
            query_for_vchain.push(query_vchain);
        }
        fs::write(
            plus_buffer.clone(),
            &serde_json::to_string_pretty(&plus_params)?,
        )?;
        fs::write(
            chain_buffer.clone(),
            &serde_json::to_string_pretty(&chain_params)?,
        )?;
        if plus_params.len() >= 10 && chain_params.len() >= 10 {
            query_for_plus = plus_params;
            query_for_vchain = chain_params;
            fs::remove_file(plus_buffer.clone())?;
            fs::remove_file(chain_buffer.clone())?;
            break;
        }
    }

    let out_path_plus = output_path.join("vchain_plus.json");
    let out_path_vchain = output_path.join("vchain.json");

    fs::write(
        out_path_plus,
        &serde_json::to_string_pretty(&query_for_plus)?,
    )?;
    fs::write(
        out_path_vchain,
        &serde_json::to_string_pretty(&query_for_vchain)?,
    )?;
    fs::remove_file(plus_buffer)?;
    fs::remove_file(chain_buffer)?;

    Ok(())
}
