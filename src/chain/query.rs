pub mod egg_qp;
pub mod query_dag;
pub mod query_param;
pub mod query_plan;

use self::{
    query_dag::DagNode,
    query_param::{param_to_qp, Node},
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
        query::{egg_qp::egg_optimize, query_dag::gen_parallel_query_dag, query_plan::QPNode},
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
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct TimeWin {
    pub start_blk: u32,
    pub end_blk: u32,
}

impl TimeWin {
    pub fn new(start_blk: u32, end_blk: u32) -> Self {
        Self { start_blk, end_blk }
    }
    pub fn get_start(&self) -> u32 {
        self.start_blk
    }
    pub fn get_end(&self) -> u32 {
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
    stage3: ProcessDuration,
    stage4: ProcessDuration,
    res: (HashMap<ObjId, Object<K>>, VO<K>),
}

#[allow(clippy::too_many_arguments)]
#[allow(clippy::type_complexity)]
fn query_final<K: Num, T: ReadInterface<K = K>>(
    chain: &T,
    pk: &AccPublicKey,
    mut query_plan: QueryPlan<K>,
    outputs: HashSet<NodeIndex>,
    time_win: &TimeWin,
    s_win_size: Option<u16>,
    e_win_size: u16,
    query_dag: &Graph<query_dag::DagNode<K>, bool>,
) -> Result<(HashMap<ObjId, Object<K>>, VO<K>)> {
    let mut vo_dag_content = HashMap::<NodeIndex, VONode<K>>::new();
    let qp_end_blk_height = query_plan.end_blk_height;
    let qp_dag_content = &mut query_plan.dag_content;
    let mut set_map = HashMap::<NodeIndex, Set>::new();
    let mut trie_ctxes = HashMap::<Height, trie_tree::read::ReadContext<T>>::new();
    let mut trie_proofs = HashMap::<Height, trie_tree::proof::Proof>::new();
    let qp_trie_proofs = query_plan.trie_proofs;
    let mut obj_map = HashMap::<ObjId, Object<K>>::new();
    let mut merkle_proofs = HashMap::<Height, MerkleProof>::new();
    let mut time_win_map = HashMap::<Height, u16>::new();

    let mut qp_inputs = match toposort(query_dag, None) {
        Ok(v) => v,
        Err(_) => {
            bail!("Input query plan graph not valid")
        }
    };
    qp_inputs.reverse();

    let mut height_dims: Vec<(Height, u8)> = Vec::new();
    for idx in qp_inputs {
        if let Some(dag_node) = query_dag.node_weight(idx) {
            match dag_node {
                query_dag::DagNode::Range(node) => {
                    let set;
                    let acc;
                    let proof;
                    if let Some(QPNode::Range(n)) = qp_dag_content.remove(&idx) {
                        height_dims.push((n.blk_height, node.dim as u8));
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
                    }
                }
                query_dag::DagNode::Union(_) => {
                    if let Some(QPNode::Union(_)) = qp_dag_content.remove(&idx) {
                        let mut child_idxs = Vec::<NodeIndex>::new();
                        for c_idx in query_dag.neighbors_directed(idx, Outgoing) {
                            child_idxs.push(c_idx);
                        }
                        let mut qp_c_idx1 = child_idxs
                            .get(1)
                            .context("Cannot find the first child idx of final difference")?;
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
                                .context("Cannot find the second child idx of final difference")?;
                        } else {
                            qp_c_idx1 = child_idxs
                                .get(0)
                                .context("Cannot find the first qp child idx of intersection")?;
                            qp_c_idx2 = child_idxs
                                .get(1)
                                .context("Cannot find the second qp child idx of intersection")?;
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
                        if !outputs.contains(&idx) {
                            let (res_set, res_acc, inter_proof) =
                                compute_set_operation_intermediate(
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
                            // should not appear
                            let (res_set, final_proof) =
                                compute_set_operation_final(Op::Union, c1_set, c2_set, pk);
                            let vo_final_union = VOFinalUnion { proof: final_proof };
                            vo_dag_content.insert(idx, VONode::FinalUnion(vo_final_union));
                            set_map.insert(idx, res_set);
                        }
                    }
                }
                query_dag::DagNode::Intersec(_) => {
                    if let Some(QPNode::Intersec(_)) = qp_dag_content.remove(&idx) {
                        let mut child_idxs = Vec::<NodeIndex>::new();
                        for c_idx in query_dag.neighbors_directed(idx, Outgoing) {
                            child_idxs.push(c_idx);
                        }
                        let mut qp_c_idx1 = child_idxs
                            .get(1)
                            .context("Cannot find the first child idx of final difference")?;
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
                                .context("Cannot find the second child idx of final difference")?;
                        } else {
                            qp_c_idx1 = child_idxs
                                .get(0)
                                .context("Cannot find the first qp child idx of intersection")?;
                            qp_c_idx2 = child_idxs
                                .get(1)
                                .context("Cannot find the second qp child idx of intersection")?;
                        }
                        if let Some(vo_c1) = vo_dag_content.get(qp_c_idx1) {
                            // vo_c2 is not empty
                            if let Some(vo_c2) = vo_dag_content.get(qp_c_idx2) {
                                // vo_c1 is not empty
                                let c1_set = set_map
                                    .get(qp_c_idx1)
                                    .context("Cannot find the set in set_map")?;
                                let c2_set = set_map
                                    .get(qp_c_idx2)
                                    .context("Cannot find the set in set_map")?;
                                if !outputs.contains(&idx) {
                                    let (res_set, res_acc, inter_proof) =
                                        compute_set_operation_intermediate(
                                            Op::Intersection,
                                            c1_set,
                                            vo_c1.get_acc()?,
                                            c2_set,
                                            vo_c2.get_acc()?,
                                            pk,
                                        );
                                    let vo_inter_intersec = VOInterIntersec {
                                        acc: res_acc,
                                        proof: Some(inter_proof),
                                    };
                                    vo_dag_content
                                        .insert(idx, VONode::InterIntersec(vo_inter_intersec));
                                    set_map.insert(idx, res_set);
                                } else {
                                    let (res_set, final_proof) = compute_set_operation_final(
                                        Op::Intersection,
                                        c1_set,
                                        c2_set,
                                        pk,
                                    );
                                    let vo_final_intersec = VOFinalIntersec { proof: final_proof };
                                    vo_dag_content
                                        .insert(idx, VONode::FinalIntersec(vo_final_intersec));
                                    set_map.insert(idx, res_set);
                                }
                            } else {
                                // vo_c1 is empty
                                let vo_inter_intersec = VOInterIntersec {
                                    acc: *vo_c1.get_acc()?,
                                    proof: None,
                                };
                                vo_dag_content
                                    .insert(idx, VONode::InterIntersec(vo_inter_intersec));
                                set_map.insert(idx, Set::new());
                            }
                        } else {
                            // vo_c2 is empty
                            let vo_c2 = vo_dag_content.get(qp_c_idx2).context(
                                "Cannot find the second child vo node in vo_dag_content",
                            )?;
                            let vo_inter_intersec = VOInterIntersec {
                                acc: *vo_c2.get_acc()?,
                                proof: None,
                            };
                            vo_dag_content.insert(idx, VONode::InterIntersec(vo_inter_intersec));
                            set_map.insert(idx, Set::new());
                        }
                    }
                }
                query_dag::DagNode::Diff(_) => {
                    if let Some(QPNode::Diff(_)) = qp_dag_content.remove(&idx) {
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
                        if let Some(vo_c2) = vo_dag_content.get(qp_c_idx2) {
                            // vo_c1 is not empty
                            let c1_set = set_map
                                .get(qp_c_idx1)
                                .context("Cannot find the set in set_map")?;
                            let c2_set = set_map
                                .get(qp_c_idx2)
                                .context("Cannot find the set in set_map")?;
                            if !outputs.contains(&idx) {
                                let (res_set, res_acc, inter_proof) =
                                    compute_set_operation_intermediate(
                                        Op::Difference,
                                        c1_set,
                                        vo_c1.get_acc()?,
                                        c2_set,
                                        vo_c2.get_acc()?,
                                        pk,
                                    );
                                let vo_inter_diff = VOInterDiff {
                                    acc: res_acc,
                                    proof: Some(inter_proof),
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
                        } else {
                            // vo_c1 is empty
                            let vo_inter_diff = VOInterDiff {
                                acc: *vo_c1.get_acc()?,
                                proof: None,
                            };
                            vo_dag_content.insert(idx, VONode::InterDiff(vo_inter_diff));
                            set_map.insert(idx, Set::new());
                        }
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

    for idx in outputs {
        let set = set_map.get(&idx).context("Cannot find set in set_map")?;
        for i in set.iter() {
            let obj_id = ObjId(*i);
            if let Some(obj_hash) = id_tree_ctx.query(obj_id, max_id_num, id_tree_fanout)? {
                let obj = chain.read_object(obj_hash)?;
                obj_map.insert(obj_id, obj);
            }
        }
    }

    let id_tree_proof = id_tree_ctx.into_proof();
    for (height, time_win) in time_win_map {
        let blk_content = chain.read_block_content(height)?;
        let obj_id_nums = blk_content.read_obj_id_nums();
        let id_set_root_hash = obj_id_nums_hash(obj_id_nums.iter());
        let mut ads_hashes = BTreeMap::<u16, Digest>::new();
        let multi_ads = blk_content.ads;
        let mut extra_bplus_rt_hashes = HashMap::<u8, Digest>::new();
        for (t_w, ads) in multi_ads.read_adses() {
            if *t_w != time_win {
                ads_hashes.insert(*t_w, ads.to_digest());
            } else {
                let bplus_tree_roots = &ads.bplus_tree_roots;
                for (i, rt) in bplus_tree_roots.iter().enumerate() {
                    extra_bplus_rt_hashes.insert(i as u8, rt.to_digest());
                }
                for (h, d) in &height_dims {
                    if *h == height {
                        extra_bplus_rt_hashes.remove(d);
                    }
                }
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
            extra_bplus_rt_hashes,
        };
        merkle_proofs.insert(height, merkle_proof);
    }
    let vo_dag_struct = VoDagContent {
        output_sets: set_map,
        dag_content: vo_dag_content,
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

fn select_win_size(win_sizes: &[u16], query_time_win: TimeWin) -> Result<Vec<(TimeWin, u16)>> {
    let mut vec_res = Vec::<(TimeWin, u16)>::new();
    let mut cur_win = query_time_win;
    let max = *win_sizes.last().context("empty time win")? as u32;

    while cur_win.get_end() + 1 >= max + cur_win.get_start() {
        let new_time_win = TimeWin::new(cur_win.get_start(), cur_win.get_start() + max - 1);
        vec_res.push((new_time_win, max as u16));
        if cur_win.get_start() + max == cur_win.get_end() + 1 {
            return Ok(vec_res);
        } else {
            cur_win = TimeWin::new(cur_win.get_start() + max, cur_win.get_end());
        }
    }
    let cur_size = (cur_win.get_end() - cur_win.get_start() + 1) as u16;
    let mut last_size = 0;
    for win_size in win_sizes {
        if cur_size <= *win_size {
            last_size = *win_size as u32;
            break;
        }
    }
    let last_win = TimeWin::new(cur_win.get_end() - last_size + 1, cur_win.get_end());
    vec_res.push((last_win, last_size as u16));
    Ok(vec_res)
}

fn paral_sub_query_process<K: Num, T: ReadInterface<K = K>>(
    empty_set: bool,
    time_win: &TimeWin,
    e_win_size: u16,
    query_dag: &Graph<query_dag::DagNode<K>, bool>,
    chain: &T,
    pk: &AccPublicKey,
) -> Result<QueryResInfo<K>> {
    let sub_timer = howlong::ProcessCPUTimer::new();
    let mut query_plan = param_to_qp(time_win, e_win_size, query_dag, chain, pk)?;
    let time1 = sub_timer.elapsed();
    let sub_timer = howlong::ProcessCPUTimer::new();
    let time2 = sub_timer.elapsed();
    let sub_timer = howlong::ProcessCPUTimer::new();
    let mut outputs;
    if empty_set {
        outputs = process_empty_sets(query_dag, &mut query_plan)?;
    } else {
        outputs = HashSet::new();
        let rt = &query_plan.root_idx;
        outputs.insert(*rt);
    }
    let time3 = sub_timer.elapsed();
    let sub_timer = howlong::ProcessCPUTimer::new();
    let res = query_final(
        chain, pk, query_plan, outputs, time_win, None, e_win_size, query_dag,
    )?;
    let time4 = sub_timer.elapsed();

    Ok(QueryResInfo {
        stage1: time1,
        stage2: time2,
        stage3: time3,
        stage4: time4,
        res,
    })
}

#[allow(clippy::type_complexity)]
fn paral_first_sub_query_with_egg<K: Num, T: ReadInterface<K = K>>(
    empty_set: bool,
    time_win: &TimeWin,
    e_win_size: u16,
    query_dag: &Graph<query_dag::DagNode<K>, bool>,
    chain: &T,
    pk: &AccPublicKey,
) -> Result<(Result<QueryResInfo<K>>, Graph<query_dag::DagNode<K>, bool>)> {
    let sub_timer = howlong::ProcessCPUTimer::new();
    let mut query_plan = param_to_qp(time_win, e_win_size, query_dag, chain, pk)?;
    let time1 = sub_timer.elapsed();
    let sub_timer = howlong::ProcessCPUTimer::new();
    let new_dag = egg_optimize(query_dag, &mut query_plan)?;
    let time2 = sub_timer.elapsed();
    let sub_timer = howlong::ProcessCPUTimer::new();

    let mut outputs;
    if empty_set {
        outputs = process_empty_sets(&new_dag, &mut query_plan)?;
    } else {
        outputs = HashSet::new();
        let rt = &query_plan.root_idx;
        outputs.insert(*rt);
    }
    let time3 = sub_timer.elapsed();
    let sub_timer = howlong::ProcessCPUTimer::new();
    let res = query_final(
        chain, pk, query_plan, outputs, time_win, None, e_win_size, &new_dag,
    )?;
    let time4 = sub_timer.elapsed();

    let query_res_info = QueryResInfo {
        stage1: time1,
        stage2: time2,
        stage3: time3,
        stage4: time4,
        res,
    };

    Ok((Ok(query_res_info), new_dag))
}

fn process_empty_sets<K: Num>(
    query_dag: &Graph<query_dag::DagNode<K>, bool>,
    qp: &mut QueryPlan<K>,
) -> Result<HashSet<NodeIndex>> {
    let qp_root_idx = qp.root_idx;
    let qp_content = qp.get_dag_cont_mut();
    let mut sub_root_idxs = HashSet::new();
    sub_root_idxs.insert(qp_root_idx);
    let mut new_qp_content = HashMap::new();
    let mut queue = VecDeque::new();
    queue.push_back(qp_root_idx);
    while let Some(idx) = queue.pop_front() {
        let query_node = query_dag
            .node_weight(idx)
            .context("node not exist in dag")?;
        match query_node {
            DagNode::Range(_) => {
                new_qp_content.insert(idx, qp_content.remove(&idx).context("")?);
            }
            DagNode::Keyword(_) => {
                new_qp_content.insert(idx, qp_content.remove(&idx).context("")?);
            }
            DagNode::BlkRt(_) => {
                new_qp_content.insert(idx, qp_content.remove(&idx).context("")?);
            }
            DagNode::Union(_) => {
                let mut child_idxs = Vec::new();
                for c_idx in query_dag.neighbors_directed(idx, Outgoing) {
                    child_idxs.push(c_idx);
                }
                if sub_root_idxs.contains(&idx) {
                    sub_root_idxs.remove(&idx);
                    for idx in &child_idxs {
                        sub_root_idxs.insert(*idx);
                    }
                } else {
                    new_qp_content.insert(idx, qp_content.remove(&idx).context("")?);
                }
                let qp_c_idx1 = child_idxs
                    .get(0)
                    .context("Cannot find the first child idx")?;
                let qp_c_idx2 = child_idxs
                    .get(1)
                    .context("Cannot find the second child idx")?;
                queue.push_back(*qp_c_idx1);
                queue.push_back(*qp_c_idx2);
            }
            DagNode::Intersec(_) => {
                let mut child_idxs = Vec::new();
                for c_idx in query_dag.neighbors_directed(idx, Outgoing) {
                    child_idxs.push(c_idx);
                }
                let qp_c_idx1 = child_idxs
                    .get(0)
                    .context("Cannot find the first child idx")?;
                let qp_c_idx2 = child_idxs
                    .get(1)
                    .context("Cannot find the second child idx")?;
                let qp_c1 = qp_content.get(qp_c_idx1).context("")?;
                let qp_c2 = qp_content.get(qp_c_idx2).context("")?;
                if qp_c1.get_set()?.is_empty() {
                    queue.push_back(*qp_c_idx1);
                    new_qp_content.insert(idx, qp_content.remove(&idx).context("")?);
                    continue;
                }
                if qp_c2.get_set()?.is_empty() {
                    queue.push_back(*qp_c_idx2);
                    new_qp_content.insert(idx, qp_content.remove(&idx).context("")?);
                    continue;
                }
                queue.push_back(*qp_c_idx1);
                queue.push_back(*qp_c_idx2);
                new_qp_content.insert(idx, qp_content.remove(&idx).context("")?);
            }
            DagNode::Diff(_) => {
                let mut child_idxs = Vec::new();
                for c_idx in query_dag.neighbors_directed(idx, Outgoing) {
                    child_idxs.push(c_idx);
                }
                let mut qp_c_idx1 = child_idxs
                    .get(1)
                    .context("Cannot find the first child idx")?;
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
                        .context("Cannot find the first qp child idx")?;
                } else {
                    qp_c_idx1 = child_idxs
                        .get(0)
                        .context("Cannot find the first qp child idx")?;
                    qp_c_idx2 = child_idxs
                        .get(1)
                        .context("Cannot find the first qp child idx")?;
                }
                let qp_c1 = qp_content.get(qp_c_idx1).context("")?;
                let qp_c2 = qp_content.get(qp_c_idx2).context("")?;

                if sub_root_idxs.contains(&idx) && qp_c2.get_set()?.is_empty() {
                    sub_root_idxs.remove(&idx);
                    for idx in &child_idxs {
                        sub_root_idxs.insert(*idx);
                    }
                    queue.push_back(*qp_c_idx1);
                    queue.push_back(*qp_c_idx2);
                    continue;
                }

                if qp_c1.get_set()?.is_empty() {
                    queue.push_back(*qp_c_idx1);
                    new_qp_content.insert(idx, qp_content.remove(&idx).context("")?);
                    continue;
                }
                queue.push_back(*qp_c_idx1);
                queue.push_back(*qp_c_idx2);
                new_qp_content.insert(idx, qp_content.remove(&idx).context("")?);
            }
        }
    }

    qp.update_dag_cont(new_qp_content);

    Ok(sub_root_idxs)
}

fn parallel_processing<K: Num, T: ReadInterface<K = K> + std::marker::Sync + std::marker::Send>(
    empty_set: bool,
    egg_opt: bool,
    complete_wins: &mut Vec<(TimeWin, u16)>,
    dag: &Graph<DagNode<K>, bool>,
    responses: &mut Vec<Result<QueryResInfo<K>>>,
    chain: &T,
    pk: &AccPublicKey,
) -> Result<Graph<DagNode<K>, bool>> {
    if egg_opt {
        if let Some((selected_win, win_size)) = complete_wins.pop() {
            let (q_res_info, new_dag) =
                paral_first_sub_query_with_egg(empty_set, &selected_win, win_size, dag, chain, pk)?;

            complete_wins
                .par_iter()
                .map(|(time_win, e_win_size)| {
                    paral_sub_query_process(empty_set, time_win, *e_win_size, &new_dag, chain, pk)
                })
                .collect_into_vec(responses);
            responses.push(q_res_info);
            Ok(new_dag)
        } else {
            bail!("Empty complete windows");
        }
    } else {
        complete_wins
            .par_iter()
            .map(|(time_win, e_win_size)| {
                paral_sub_query_process(empty_set, time_win, *e_win_size, dag, chain, pk)
            })
            .collect_into_vec(responses);
        Ok(dag.clone())
    }
}

#[allow(clippy::type_complexity)]
pub fn query<K: Num, T: ReadInterface<K = K> + std::marker::Sync + std::marker::Send>(
    empty_set: bool,
    egg_opt: bool,
    chain: T,
    query_param: QueryParam<K>,
    pk: &AccPublicKey,
) -> Result<(
    Vec<(HashMap<ObjId, Object<K>>, VO<K>)>,
    Graph<DagNode<K>, bool>,
    QueryTime,
)> {
    let chain_param = &chain.get_parameter()?;
    let chain_win_sizes = &chain_param.time_win_sizes;
    let timer = howlong::ProcessCPUTimer::new();
    let query_time_win = query_param.gen_time_win();
    let query_content = query_param.gen_query_content();
    let mut complete_wins = select_win_size(chain_win_sizes, query_time_win)?;
    let mut responses = Vec::with_capacity(complete_wins.len());
    let dag = gen_parallel_query_dag(&query_content)?;
    let res_dag = parallel_processing(
        empty_set,
        egg_opt,
        &mut complete_wins,
        &dag,
        &mut responses,
        &chain,
        pk,
    )?;
    let total_query_time = Time::from(timer.elapsed());

    let mut stage1_time = Vec::<ProcessDuration>::new();
    let mut stage2_time = Vec::<ProcessDuration>::new();
    let mut stage3_time = Vec::<ProcessDuration>::new();
    let mut stage4_time = Vec::<ProcessDuration>::new();
    let mut result = Vec::<(HashMap<ObjId, Object<K>>, VO<K>)>::new();
    for response in responses {
        let a = response?;
        stage1_time.push(a.stage1);
        stage2_time.push(a.stage2);
        stage3_time.push(a.stage3);
        stage4_time.push(a.stage4);
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
    let mut stage3_total_time: ProcessDuration = ProcessDuration::default();
    for t in stage3_time {
        stage3_total_time += t;
    }
    let mut stage4_total_time: ProcessDuration = ProcessDuration::default();
    for t in stage4_time {
        stage4_total_time += t;
    }
    let query_time = QueryTime {
        stage1: Time::from(stage1_total_time),
        stage2: Time::from(stage2_total_time),
        stage3: Time::from(stage3_total_time),
        stage4: Time::from(stage4_total_time),
        total: total_query_time,
    };
    Ok((result, res_dag, query_time))
}

#[cfg(test)]
mod tests {
    use super::TimeWin;
    use crate::chain::query::select_win_size;

    #[test]
    fn test_select_win_size() {
        let query_time_win = TimeWin::new(1, 10);
        let res = select_win_size(&vec![2, 4, 8], query_time_win).unwrap();
        let exp = vec![(TimeWin::new(1, 8), 8), (TimeWin::new(9, 10), 2)];
        assert_eq!(res, exp);
        let query_time_win = TimeWin::new(1, 12);
        let res = select_win_size(&vec![2, 4, 8], query_time_win).unwrap();
        let exp = vec![(TimeWin::new(1, 8), 8), (TimeWin::new(9, 12), 4)];
        assert_eq!(res, exp);
        let query_time_win = TimeWin::new(1, 13);
        let res = select_win_size(&vec![2, 4, 8], query_time_win).unwrap();
        let exp = vec![(TimeWin::new(1, 8), 8), (TimeWin::new(6, 13), 8)];
        assert_eq!(res, exp);
        let query_time_win = TimeWin::new(1, 14);
        let res = select_win_size(&vec![2, 4, 8], query_time_win).unwrap();
        let exp = vec![(TimeWin::new(1, 8), 8), (TimeWin::new(7, 14), 8)];
        assert_eq!(res, exp);
    }
}
