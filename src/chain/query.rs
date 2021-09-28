pub mod egg_qp;
pub mod query_dag;
pub mod query_param;
pub mod query_plan;

use self::{
    query_dag::DagNode,
    query_param::{param_to_qp_parallel, Node},
};
use crate::{
    acc::{
        compute_set_operation_final, compute_set_operation_intermediate, ops::Op, AccPublicKey, Set,
    },
    chain::{
        block::{hash::obj_id_nums_hash, Height},
        bplus_tree,
        id_tree::{self, ObjId},
        object::Object,
        query::{
            query_dag::{
                gen_last_query_dag_with_cont_basic, gen_last_query_dag_with_cont_trimmed,
                gen_parallel_query_dag,
            },
            query_plan::QPNode,
        },
        range::Range,
        traits::{Num, ReadInterface},
        trie_tree,
        verify::vo::{
            MerkleProof, VOBlkRtNode, VOFinalDiff, VOFinalIntersec, VOFinalUnion, VOInterDiff,
            VOInterIntersec, VOInterUnion, VOKeywordNode, VONode, VORangeNode, VoDagContent, VO,
        },
    },
    digest::{Digest, Digestible},
    utils::{QueryTime, Time},
};
use anyhow::{bail, Context, Result};
use howlong::ProcessDuration;
use petgraph::algo::toposort;
use petgraph::{graph::NodeIndex, EdgeDirection::Outgoing, Graph};
use query_param::QueryParam;
use query_plan::QueryPlan;
use rayon::prelude::*;
use smol_str::SmolStr;
use std::collections::{BTreeMap, HashMap};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct TimeWin {
    pub start_blk: u64,
    pub end_blk: u64,
}

impl TimeWin {
    pub fn new(start_blk: u64, end_blk: u64) -> Self {
        Self { start_blk, end_blk }
    }
    pub fn get_start(&self) -> u64 {
        self.start_blk
    }
    pub fn get_end(&self) -> u64 {
        self.end_blk
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QueryContent<K: Num> {
    pub range: Vec<Range<K>>,
    pub keyword_exp: Option<Node>,
}

pub struct QueryResInfo<K: Num> {
    stage1: ProcessDuration,
    stage2: ProcessDuration,
    res: (HashMap<ObjId, Object<K>>, VO<K>),
}

#[allow(clippy::too_many_arguments)]
#[allow(clippy::type_complexity)]
fn query_final<K: Num, T: ReadInterface<K = K>>(
    chain: &T,
    pk: &AccPublicKey,
    mut query_plan: QueryPlan<K>,
    time_win: &TimeWin,
    s_win_size: Option<u64>,
    e_win_size: u64,
    graph_idx: usize,
    query_dag: &Graph<query_dag::DagNode<K>, bool>,
) -> Result<(HashMap<ObjId, Object<K>>, VO<K>)> {
    let mut vo_dag_content = HashMap::<NodeIndex, VONode<K>>::new();
    let qp_root_idx = query_plan.root_idx;
    let qp_end_blk_height = query_plan.end_blk_height;
    let qp_dag_content = &mut query_plan.dag_content;
    let mut set_map = HashMap::<NodeIndex, Set>::new();
    let mut trie_ctxes = HashMap::<Height, trie_tree::read::ReadContext<T>>::new();
    let mut trie_proofs = HashMap::<Height, trie_tree::proof::Proof>::new();
    let qp_trie_proofs = query_plan.trie_proofs;
    let mut obj_map = HashMap::<ObjId, Object<K>>::new();
    let mut merkle_proofs = HashMap::<Height, MerkleProof>::new();
    let mut time_win_map = HashMap::<Height, u64>::new();

    let mut qp_inputs = match toposort(query_dag, None) {
        Ok(v) => v,
        Err(_) => {
            bail!("Input query plan graph not valid")
        }
    };
    qp_inputs.reverse();

    for idx in qp_inputs {
        if let Some(dag_node) = query_dag.node_weight(idx) {
            match dag_node {
                query_dag::DagNode::Range(node) => {
                    let set;
                    let acc;
                    let proof;
                    if let Some(QPNode::Range(n)) = qp_dag_content.remove(&idx) {
                        let blk_height = n.blk_height;
                        let win_size = if blk_height.0 == time_win.get_end() {
                            e_win_size
                        } else if blk_height.0 == time_win.get_start() - 1 {
                            s_win_size.context(
                                "hight = start time_win height but start win_size is None",
                            )?
                        } else {
                            bail!("invalid blk height");
                        };
                        time_win_map.insert(blk_height, win_size);
                        if let Some((s, a, p)) = n.set {
                            set = s;
                            acc = a;
                            proof = p;
                        } else {
                            let bplus_root = chain
                                .read_block_content(blk_height)?
                                .ads
                                .read_bplus_root(win_size, node.dim)?;
                            let (s, a, p) = bplus_tree::read::range_query(
                                chain,
                                bplus_root.bplus_tree_root_id,
                                node.range,
                                pk,
                            )?;
                            set = s;
                            acc = a;
                            proof = p;
                        }
                        let vo_range_node = VORangeNode {
                            blk_height: n.blk_height,
                            win_size,
                            acc,
                            proof,
                        };
                        vo_dag_content.insert(idx, VONode::Range(vo_range_node));
                        set_map.insert(idx, set);
                    } else {
                        bail!("QPNode with idx {:?} does not exist in query plan", idx);
                    }
                }
                query_dag::DagNode::Keyword(node) => {
                    let set;
                    let acc;
                    if let Some(QPNode::Keyword(n)) = qp_dag_content.remove(&idx) {
                        let blk_height = n.blk_height;
                        let win_size = if blk_height.0 == time_win.get_end() {
                            e_win_size
                        } else if blk_height.0 == time_win.get_start() - 1 {
                            s_win_size.context(
                                "hight = start time_win height but start win_size is None",
                            )?
                        } else {
                            bail!("invalid blk height");
                        };
                        time_win_map.insert(blk_height, win_size);
                        if let Some((s, a)) = n.set {
                            set = s;
                            acc = a;
                        } else if let Some(ctx) = trie_ctxes.get_mut(&n.blk_height) {
                            let trie_ctx = ctx;
                            let (s, a) = trie_ctx.query(&SmolStr::from(&node.keyword), pk)?;
                            set = s;
                            acc = a;
                        } else {
                            let trie_root = chain
                                .read_block_content(blk_height)?
                                .ads
                                .read_trie_root(win_size)?;
                            let mut trie_ctx =
                                trie_tree::read::ReadContext::new(chain, trie_root.trie_root_id);
                            let (s, a) = trie_ctx.query(&SmolStr::from(&node.keyword), pk)?;
                            set = s;
                            acc = a;
                            trie_ctxes.insert(n.blk_height, trie_ctx);
                        }
                        let vo_keyword_node = VOKeywordNode {
                            blk_height: n.blk_height,
                            win_size,
                            acc,
                        };
                        vo_dag_content.insert(idx, VONode::Keyword(vo_keyword_node));
                        set_map.insert(idx, set);
                    } else {
                        bail!("QPNode with idx {:?} does not exist in query plan", idx);
                    }
                }
                query_dag::DagNode::BlkRt(_) => {
                    let set;
                    let acc;
                    if let Some(QPNode::BlkRt(n)) = qp_dag_content.remove(&idx) {
                        let blk_height = n.blk_height;
                        let win_size = if blk_height.0 == time_win.get_end() {
                            e_win_size
                        } else if blk_height.0 == time_win.get_start() - 1 {
                            s_win_size.context(
                                "hight = start time_win height but start win_size is None",
                            )?
                        } else {
                            bail!("invalid blk height");
                        };
                        time_win_map.insert(blk_height, win_size);
                        if let Some((s, a)) = n.set {
                            set = s;
                            acc = a;
                        } else {
                            let blk_content = chain.read_block_content(blk_height)?;
                            let bplus_root = blk_content.ads.read_bplus_root(win_size, 0)?;
                            let bplus_root_id =
                                bplus_root.bplus_tree_root_id.context("Empty bplus root")?;
                            let bplus_root_node =
                                bplus_tree::BPlusTreeNodeLoader::load_node(chain, bplus_root_id)?;
                            set = bplus_root_node.get_set().clone();
                            acc = bplus_root_node.get_node_acc();
                        }
                        let vo_blk_root = VOBlkRtNode {
                            blk_height: n.blk_height,
                            win_size,
                            acc,
                        };
                        vo_dag_content.insert(idx, VONode::BlkRt(vo_blk_root));
                        set_map.insert(idx, set);
                    } else {
                        bail!("QPNode with idx {:?} does not exist in query plan", idx);
                    }
                }
                query_dag::DagNode::Union(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for c_idx in query_dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(c_idx);
                    }
                    let qp_c_idx1 = child_idxs
                        .get(0)
                        .context("Cannot find the first qp child idx of union")?;
                    let vo_c1 = vo_dag_content
                        .get(qp_c_idx1)
                        .context("Cannot find the first child vo node in vo_dag_content")?;
                    let c1_set = set_map
                        .get(qp_c_idx1)
                        .context("Cannot find the set in set_map")?;
                    let qp_c_idx2 = child_idxs
                        .get(1)
                        .context("Cannot find the second qp child idx of union")?;
                    let vo_c2 = vo_dag_content
                        .get(qp_c_idx2)
                        .context("Cannot find the second child vo node in vo_dag_content")?;
                    let c2_set = set_map
                        .get(qp_c_idx2)
                        .context("Cannot find the set in set_map")?;
                    if qp_root_idx != idx {
                        let (res_set, res_acc, inter_proof) = compute_set_operation_intermediate(
                            Op::Union,
                            c1_set,
                            vo_c1.get_acc()?,
                            c2_set,
                            vo_c2.get_acc()?,
                            pk,
                        );
                        let vo_inter_union = VOInterUnion {
                            acc: res_acc,
                            proof: inter_proof,
                        };
                        vo_dag_content.insert(idx, VONode::InterUnion(vo_inter_union));
                        set_map.insert(idx, res_set);
                    } else {
                        let (res_set, final_proof) =
                            compute_set_operation_final(Op::Union, c1_set, c2_set, pk);
                        let vo_final_union = VOFinalUnion { proof: final_proof };
                        vo_dag_content.insert(idx, VONode::FinalUnion(vo_final_union));
                        set_map.insert(idx, res_set);
                    }
                }
                query_dag::DagNode::Intersec(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for c_idx in query_dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(c_idx);
                    }
                    let qp_c_idx1 = child_idxs
                        .get(0)
                        .context("Cannot find the first qp child idx of intersection")?;
                    let vo_c1 = vo_dag_content
                        .get(qp_c_idx1)
                        .context("Cannot find the first child vo node in vo_dag_content")?;
                    let c1_set = set_map
                        .get(qp_c_idx1)
                        .context("Cannot find the set in set_map")?;
                    let qp_c_idx2 = child_idxs
                        .get(1)
                        .context("Cannot find the second qp child idx of union")?;
                    let vo_c2 = vo_dag_content
                        .get(qp_c_idx2)
                        .context("Cannot find the second child vo node in vo_dag_content")?;
                    let c2_set = set_map
                        .get(qp_c_idx2)
                        .context("Cannot find the set in set_map")?;
                    if qp_root_idx != idx {
                        let (res_set, res_acc, inter_proof) = compute_set_operation_intermediate(
                            Op::Intersection,
                            c1_set,
                            vo_c1.get_acc()?,
                            c2_set,
                            vo_c2.get_acc()?,
                            pk,
                        );
                        let vo_inter_intersec = VOInterIntersec {
                            acc: res_acc,
                            proof: inter_proof,
                        };
                        vo_dag_content.insert(idx, VONode::InterIntersec(vo_inter_intersec));
                        set_map.insert(idx, res_set);
                    } else {
                        let (res_set, final_proof) =
                            compute_set_operation_final(Op::Intersection, c1_set, c2_set, pk);
                        let vo_final_intersec = VOFinalIntersec { proof: final_proof };
                        vo_dag_content.insert(idx, VONode::FinalIntersec(vo_final_intersec));
                        set_map.insert(idx, res_set);
                    }
                }
                query_dag::DagNode::Diff(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for c_idx in query_dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(c_idx);
                    }
                    let mut qp_c_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first qp child idx of difference")?;
                    let qp_c_idx2;
                    let edge_idx = query_dag
                        .find_edge(idx, *qp_c_idx1)
                        .context("Cannot find edge")?;
                    let weight = query_dag
                        .edge_weight(edge_idx)
                        .context("Cannot find edge")?;
                    if !*weight {
                        qp_c_idx2 = child_idxs
                            .get(0)
                            .context("Cannot find the first qp child idx of difference")?;
                    } else {
                        qp_c_idx1 = child_idxs
                            .get(0)
                            .context("Cannot find the first qp child idx of difference")?;
                        qp_c_idx2 = child_idxs
                            .get(1)
                            .context("Cannot find the first qp child idx of difference")?;
                    }
                    let vo_c1 = vo_dag_content
                        .get(qp_c_idx1)
                        .context("Cannot find the first child vo node in vo_dag_content")?;
                    let c1_set = set_map
                        .get(qp_c_idx1)
                        .context("Cannot find the set in set_map")?;
                    let vo_c2 = vo_dag_content
                        .get(qp_c_idx2)
                        .context("Cannot find the second child vo node in vo_dag_content")?;
                    let c2_set = set_map
                        .get(qp_c_idx2)
                        .context("Cannot find the set in set_map")?;
                    if qp_root_idx != idx {
                        let (res_set, res_acc, inter_proof) = compute_set_operation_intermediate(
                            Op::Difference,
                            c1_set,
                            vo_c1.get_acc()?,
                            c2_set,
                            vo_c2.get_acc()?,
                            pk,
                        );
                        let vo_inter_diff = VOInterDiff {
                            acc: res_acc,
                            proof: inter_proof,
                        };
                        vo_dag_content.insert(idx, VONode::InterDiff(vo_inter_diff));
                        set_map.insert(idx, res_set);
                    } else {
                        let (res_set, final_proof) =
                            compute_set_operation_final(Op::Difference, c1_set, c2_set, pk);
                        let vo_final_diff = VOFinalDiff { proof: final_proof };
                        vo_dag_content.insert(idx, VONode::FinalDiff(vo_final_diff));
                        set_map.insert(idx, res_set);
                    }
                }
            }
        }
    }

    for (height, trie_ctx) in trie_ctxes {
        let trie_proof = trie_ctx.into_proof();
        trie_proofs.insert(height, trie_proof);
    }
    for (height, trie_proof) in qp_trie_proofs {
        trie_proofs.insert(height, trie_proof);
    }

    // in case of range query only && last sub-query has start sub-dag
    for (height, time_win) in &time_win_map {
        if trie_proofs.get(height).is_none() {
            let trie_root = chain
                .read_block_content(*height)?
                .ads
                .read_trie_root(*time_win)?;
            let trie_ctx = trie_tree::read::ReadContext::new(chain, trie_root.trie_root_id);
            let trie_proof = trie_ctx.into_proof();
            trie_proofs.insert(*height, trie_proof);
        }
    }
    let id_root = chain.read_block_content(qp_end_blk_height)?.id_tree_root;
    let cur_obj_id = id_root.get_cur_obj_id();
    let mut id_tree_ctx = id_tree::read::ReadContext::new(chain, id_root.get_id_tree_root_id());
    let param = chain.get_parameter()?;
    let max_id_num = param.max_id_num;
    let id_tree_fanout = param.id_tree_fanout;
    let mut vo_ouput_sets = HashMap::<NodeIndex, Set>::new();

    let set = set_map
        .remove(&qp_root_idx)
        .context("Cannot find set in set_map")?;
    let mut delta_set = Set::new();
    for i in set.iter() {
        let obj_id = ObjId(*i);
        let obj_hash_opt = id_tree_ctx.query(obj_id, max_id_num, id_tree_fanout)?;
        let obj_hash;
        match obj_hash_opt {
            Some(d) => obj_hash = d,
            None => {
                delta_set = &delta_set | &Set::from_single_element(*i);
                continue;
            }
        }
        let obj = chain.read_object(obj_hash)?;
        obj_map.insert(obj_id, obj);
    }
    let sub_res_set = &set / &delta_set;
    vo_ouput_sets.insert(qp_root_idx, sub_res_set);

    let id_tree_proof = id_tree_ctx.into_proof();
    for (height, time_win) in time_win_map {
        let blk_content = chain.read_block_content(height)?;
        let obj_id_nums = blk_content.read_obj_id_nums();
        let id_set_root_hash = obj_id_nums_hash(obj_id_nums.iter());
        let mut ads_hashes = BTreeMap::<u64, Digest>::new();
        let multi_ads = blk_content.ads;
        for (t_w, ads) in multi_ads.read_adses() {
            if *t_w != time_win {
                ads_hashes.insert(*t_w, ads.to_digest());
            }
        }

        let id_tree_root_hash = if height == qp_end_blk_height {
            None
        } else {
            Some(chain.read_block_content(height)?.id_tree_root.to_digest())
        };
        let merkle_proof = MerkleProof {
            id_tree_root_hash,
            id_set_root_hash,
            ads_hashes,
        };
        merkle_proofs.insert(height, merkle_proof);
    }
    let vo_dag_struct = VoDagContent {
        output_sets: vo_ouput_sets,
        dag_content: vo_dag_content,
        dag_idx: graph_idx,
    };
    let vo = VO {
        vo_dag_content: vo_dag_struct,
        trie_proofs,
        id_tree_proof,
        cur_obj_id,
        merkle_proofs,
    };
    Ok((obj_map, vo))
}

#[allow(clippy::type_complexity)]
fn select_win_size(
    win_sizes: &[u64],
    query_time_win: TimeWin,
) -> Result<(Vec<(TimeWin, u64)>, Option<(TimeWin, Option<u64>, u64)>)> {
    let mut vec_res = Vec::<(TimeWin, u64)>::new();
    let mut cur_win = query_time_win;
    let max = win_sizes.last().context("empty time win")?;
    while cur_win.get_end() + 1 >= max + cur_win.get_start() {
        let new_time_win = TimeWin::new(cur_win.get_start(), cur_win.get_start() + max - 1);
        vec_res.push((new_time_win, *max));
        if cur_win.get_start() + *max == cur_win.get_end() + 1 {
            return Ok((vec_res, None));
        } else {
            cur_win = TimeWin::new(cur_win.get_start() + *max, cur_win.get_end());
        }
    }

    let cur_size = cur_win.get_end() - cur_win.get_start() + 1;
    let mut end_idx = 0;
    for (i, win_size) in win_sizes.iter().enumerate() {
        if cur_size <= *win_size {
            end_idx = i;
            break;
        }
    }
    let higher = win_sizes.get(end_idx).context("cannot find size")?;
    let last_win;
    if cur_size == *higher {
        last_win = (cur_win, None, *higher);
    } else {
        let mut start_idx = 0;
        let mut lower = *win_sizes.get(start_idx).context("not time window")?;
        while cur_win.get_start() > lower
            && cur_win.get_start() + higher > cur_win.get_end() + lower
        {
            start_idx += 1;
            lower = *win_sizes.get(start_idx).context("no time win")?;
        }
        last_win = (cur_win, Some(lower), *higher);
    }
    Ok((vec_res, Some(last_win)))
}

fn paral_sub_query_process<K: Num, T: ReadInterface<K = K>>(
    time_win: &TimeWin,
    e_win_size: u64,
    query_dag: &Graph<query_dag::DagNode<K>, bool>,
    chain: &T,
    pk: &AccPublicKey,
) -> Result<QueryResInfo<K>> {
    let sub_timer = howlong::ProcessCPUTimer::new();
    let query_plan = param_to_qp_parallel(time_win, e_win_size, query_dag, chain, pk)?;
    let time1 = sub_timer.elapsed();
    let sub_timer = howlong::ProcessCPUTimer::new();
    let res = query_final(
        chain, pk, query_plan, time_win, None, e_win_size, 0, query_dag,
    )?;
    let time2 = sub_timer.elapsed();
    Ok(QueryResInfo {
        stage1: time1,
        stage2: time2,
        res,
    })
}

#[allow(clippy::too_many_arguments)]
fn last_sub_query_process<K: Num, T: ReadInterface<K = K>>(
    opt_level: u8,
    time_win: &TimeWin,
    s_win_size: Option<u64>,
    e_win_size: u64,
    query_dag: Graph<query_dag::DagNode<K>, bool>,
    query_content: &QueryContent<K>,
    chain: &T,
    pk: &AccPublicKey,
    graph_map: &mut HashMap<usize, Graph<DagNode<K>, bool>>,
) -> Result<QueryResInfo<K>> {
    let sub_timer = howlong::ProcessCPUTimer::new();

    let (dag2, qp2) = match opt_level {
        0 => gen_last_query_dag_with_cont_basic(time_win, s_win_size, query_dag)?,
        1 => gen_last_query_dag_with_cont_trimmed(
            time_win,
            s_win_size,
            e_win_size,
            query_dag,
            query_content,
            chain,
            pk,
        )?,
        _ => bail!("invalid optimization level"),
    };

    let time1 = sub_timer.elapsed();
    let sub_timer = howlong::ProcessCPUTimer::new();
    let res = query_final(chain, pk, qp2, time_win, s_win_size, e_win_size, 1, &dag2)?;
    let time2 = sub_timer.elapsed();
    graph_map.insert(1, dag2);

    Ok(QueryResInfo {
        stage1: time1,
        stage2: time2,
        res,
    })
}

#[allow(clippy::type_complexity)]
pub fn query<K: Num, T: ReadInterface<K = K> + std::marker::Sync + std::marker::Send>(
    opt_level: u8,
    chain: T,
    query_param: QueryParam<K>,
    pk: &AccPublicKey,
) -> Result<(
    Vec<(HashMap<ObjId, Object<K>>, VO<K>)>,
    HashMap<usize, Graph<DagNode<K>, bool>>,
    QueryTime,
)> {
    let chain_param = &chain.get_parameter()?;
    let chain_win_sizes = &chain_param.time_win_sizes;
    let timer = howlong::ProcessCPUTimer::new();
    let mut graph_map = HashMap::<usize, Graph<DagNode<K>, bool>>::new();
    let query_time_win = query_param.gen_time_win();
    let query_content = query_param.gen_query_content();
    let (complete_wins, final_win) = select_win_size(chain_win_sizes, query_time_win)?;

    // process dag1 parallel
    let dag1 = gen_parallel_query_dag(&query_content)?;
    let mut responses = Vec::with_capacity(complete_wins.len());
    complete_wins
        .par_iter()
        .map(|(time_win, e_win_size)| {
            paral_sub_query_process(time_win, *e_win_size, &dag1, &chain, pk)
        })
        .collect_into_vec(&mut responses);
    graph_map.insert(0, dag1.clone());

    // process dag2 if exists
    if let Some((time_win, s_win_size, e_win_size)) = final_win {
        let last_response = last_sub_query_process(
            opt_level,
            &time_win,
            s_win_size,
            e_win_size,
            dag1,
            &query_content,
            &chain,
            pk,
            &mut graph_map,
        );
        responses.push(last_response);
    }
    let total_query_time = Time::from(timer.elapsed());

    let mut stage1_time = Vec::<ProcessDuration>::new();
    let mut stage2_time = Vec::<ProcessDuration>::new();
    let mut result = Vec::<(HashMap<ObjId, Object<K>>, VO<K>)>::new();
    for response in responses {
        let a = response?;
        stage1_time.push(a.stage1);
        stage2_time.push(a.stage2);
        result.push(a.res);
    }

    let mut stage1_total_time: ProcessDuration = ProcessDuration::default();
    for t in stage1_time {
        stage1_total_time += t;
    }
    let mut stage2_total_time: ProcessDuration = ProcessDuration::default();
    for t in stage2_time {
        stage2_total_time += t;
    }
    let query_time = QueryTime {
        stage1: Time::from(stage1_total_time),
        stage2: Time::from(stage2_total_time),
        total: total_query_time,
    };
    Ok((result, graph_map, query_time))
}

#[cfg(test)]
mod tests {
    use super::TimeWin;
    use crate::chain::query::select_win_size;

    #[test]
    fn test_select_win_size() {
        let query_time_win = TimeWin::new(1, 12);
        let res = select_win_size(&vec![2, 4, 8], query_time_win).unwrap();
        let exp = (
            vec![(TimeWin::new(1, 8), 8)],
            Some((TimeWin::new(9, 12), None, 4)),
        );
        assert_eq!(res, exp);
        let query_time_win = TimeWin::new(1, 13);
        let res = select_win_size(&vec![2, 4, 8], query_time_win).unwrap();
        let exp = (
            vec![(TimeWin::new(1, 8), 8)],
            Some((TimeWin::new(9, 13), Some(4), 8)),
        );
        assert_eq!(res, exp);
        let query_time_win = TimeWin::new(1, 14);
        let res = select_win_size(&vec![2, 4, 8], query_time_win).unwrap();
        let exp = (
            vec![(TimeWin::new(1, 8), 8)],
            Some((TimeWin::new(9, 14), Some(4), 8)),
        );
        assert_eq!(res, exp);
    }
}
