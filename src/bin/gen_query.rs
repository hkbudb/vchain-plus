use anyhow::{bail, Context, Result};
use rand::{seq::SliceRandom, Rng};
use serde_json::json;
use std::{
    collections::{BTreeMap, HashSet},
    fs,
    iter::FromIterator,
    path::PathBuf,
};
use structopt::StructOpt;
use vchain_plus::{
    chain::{
        block::Height,
        query::query_param::{AndNode, Node, NotNode, OrNode, QueryParam},
        range::Range,
        traits::ScanQueryInterface,
    },
    digest::Digest,
    SimChain,
};

const QUERY_NUM: usize = 10;
const ERR_RATE: f64 = 0.0001;

fn gen_range_query<T: ScanQueryInterface<K = u32>>(
    time_win: u64,
    selectivity: f64,
    err_rate: f64,
    dim_num: usize,
    chain: T,
) -> Result<(String, String)> {
    let mut rng = rand::thread_rng();
    let (obj_num, blk_num, num_scopes) = chain.get_range_info(dim_num)?;
    let mut start_blk_height;
    let mut end_blk_height;
    loop {
        start_blk_height = Height(rng.gen_range(1..blk_num));
        end_blk_height = Height(start_blk_height.0 + time_win);
        if end_blk_height.0 <= blk_num {
            break;
        }
    }
    let height_selectivity = (end_blk_height.0 - start_blk_height.0) as f64 / blk_num as f64;
    let dim_selectivity = selectivity / height_selectivity;
    let sub_selectivity = dim_selectivity.powf(1_f64 / dim_num as f64);
    let mut sub_results = BTreeMap::<usize, (Range<u32>, usize, HashSet<Digest>)>::new();
    let mut cur_res_set = HashSet::<Digest>::new();
    let mut flag = true;
    for (dim, range) in num_scopes.iter().enumerate() {
        let selected_len = (obj_num as f64 * sub_selectivity) as u32;
        let mut start_p;
        let mut end_p;
        loop {
            start_p = rng.gen_range(range.get_low()..range.get_high());
            end_p = start_p + selected_len;
            if end_p <= range.get_high() {
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
        sub_results.insert(sub_res.len(), (sub_range, dim, sub_res));
    }

    while cur_res_set.len() < (obj_num as f64 * (selectivity - err_rate)) as usize
        || cur_res_set.len() > (obj_num as f64 * (selectivity + err_rate)) as usize
    {
        flag = true;
        let new_sub_range;
        let modified_dim;
        if cur_res_set.len() < (obj_num as f64 * (selectivity - err_rate)) as usize {
            let (sub_res_size, (sub_range, dim, _)) = sub_results
                .iter()
                .next()
                .context("The BTreeMap does not have min key value pair")?;
            let l = sub_range.get_low();
            let h = sub_range.get_high();
            if h + 1
                < num_scopes
                    .get(*dim)
                    .context("Range does not exist")?
                    .get_high()
            {
                new_sub_range = Range::new(l, h + 1);
            } else {
                new_sub_range = Range::new(l - 1, h);
            }
            modified_dim = *dim;
            let removed_key = *sub_res_size;
            sub_results.remove(&removed_key);
        } else {
            let (sub_res_size, (sub_range, dim, _)) = sub_results
                .iter()
                .next_back()
                .context("The BTreeMap does not have min key value pair")?;
            let l = sub_range.get_low();
            let h = sub_range.get_high();
            if h > l {
                new_sub_range = Range::new(l, h - 1);
            } else {
                bail!("Cannot reduce the range anymore");
            }
            modified_dim = *dim;
            let removed_key = *sub_res_size;
            sub_results.remove(&removed_key);
        }
        let new_sub_res = chain.range_query(
            new_sub_range,
            start_blk_height,
            end_blk_height,
            modified_dim,
        )?;
        sub_results.insert(
            new_sub_res.len(),
            (new_sub_range, modified_dim, new_sub_res),
        );

        for (_, _, sub_res) in sub_results.values() {
            if flag {
                cur_res_set = sub_res.clone();
                flag = false;
            } else {
                cur_res_set = cur_res_set.intersection(&sub_res).cloned().collect();
            }
        }
    }

    let mut ranges = BTreeMap::<usize, Range<u32>>::new();
    for (_, (r, dim, _)) in sub_results {
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
    time_win: u64,
    with_not: bool,
    not_prob: f64,
    keyword_num: usize,
    chain: T,
) -> Result<(String, String)> {
    let (blk_num, keyword_domain) = chain.get_keyword_info()?;
    let keyword_vec = Vec::from_iter(keyword_domain);
    let keywords_selected: Vec<&String> = keyword_vec
        .choose_multiple(&mut rand::thread_rng(), keyword_num)
        .collect();

    let mut rng = rand::thread_rng();
    let mut lock = false;
    let mut node: Node = Node::Input("init".to_string());
    for keyword in keywords_selected {
        if lock {
            let idx = rng.gen_range(0..2); // 0: and, 1: or
            if idx == 0 {
                if with_not {
                    node = Node::And(Box::new(AndNode(
                        node,
                        gen_node_with_not(not_prob, keyword.to_string()),
                    )));
                } else {
                    node = Node::And(Box::new(AndNode(node, Node::Input(keyword.to_string()))));
                }
            } else if with_not {
                node = Node::Or(Box::new(OrNode(
                    node,
                    gen_node_with_not(not_prob, keyword.to_string()),
                )));
            } else {
                node = Node::Or(Box::new(OrNode(node, Node::Input(keyword.to_string()))));
            }
        } else {
            if with_not {
                node = gen_node_with_not(not_prob, keyword.to_string())
            } else {
                node = Node::Input(keyword.to_string());
            }
            lock = true;
        }
    }

    let cnf_set = node.to_cnf_set();
    let cnf_node = Node::set_to_cnf(&cnf_set);

    let mut start_blk_height_num;
    let mut end_blk_height_num;
    loop {
        start_blk_height_num = rng.gen_range(1..blk_num);
        end_blk_height_num = start_blk_height_num + time_win;
        if end_blk_height_num <= blk_num {
            break;
        }
    }
    let query_param = QueryParam {
        start_blk: start_blk_height_num,
        end_blk: end_blk_height_num,
        range: Vec::<Range<u32>>::new(),
        keyword_exp: Some(cnf_node),
    };
    let vchain_plus_query_param = serde_json::to_string_pretty(&query_param)?;

    let mut total_bool = vec![];
    for n in &cnf_set {
        let keys: Vec<&String> = get_exp_str(n).into_iter().collect();
        let arr: Vec<String> = keys.into_iter().cloned().collect();
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

    /// probability of not opt
    #[structopt(short, long, default_value = "0.0")]
    prob_not: f64,

    /// query time window size
    #[structopt(short, long)]
    time_win: u64,

    /// dim number
    #[structopt(short, long, default_value = "1")]
    dim_num: usize,

    /// selectivity for range query
    #[structopt(short, long)]
    selectivities: Vec<f64>,

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

fn main() -> Result<()> {
    let opts = Opt::from_args();
    let output_path = opts.output;
    fs::create_dir_all(&output_path)?;
    let chain = SimChain::open(&opts.input)?;
    let time_win = opts.time_win;
    let mut query_for_plus = HashSet::<String>::new();
    let mut query_for_vchain = HashSet::<String>::new();
    if opts.range {
        for selectivity in &opts.selectivities {
            for _ in 0..QUERY_NUM {
                let (q_for_plus, q_for_vchain) =
                    gen_range_query(time_win, *selectivity, ERR_RATE, opts.dim_num, &chain)?;
                query_for_plus.insert(q_for_plus);
                query_for_vchain.insert(q_for_vchain);
            }
        }
    } else if opts.keyword {
        for _ in 0..QUERY_NUM {
            let (q_for_plus, q_for_vchain) =
                gen_keyword_query(time_win, opts.with_not, opts.prob_not, opts.num_keywords, &chain)?;
            query_for_plus.insert(q_for_plus);
            query_for_vchain.insert(q_for_vchain);
        }
    } else if opts.both {
        // to be implemented
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

    Ok(())
}
