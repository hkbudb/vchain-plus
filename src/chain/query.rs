pub mod egg_qp;
pub mod query_obj;
pub mod query_param;
pub mod query_plan;

use self::query_param::Node;
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
            query_obj::query_to_qp,
            query_param::{param_to_query_basic, param_to_query_trimmed2},
            query_plan::QPNode,
        },
        range::Range,
        traits::ScanQueryInterface,
        traits::{Num, ReadInterface},
        trie_tree,
        verify::vo::{
            MerkleProof, VOBlkRtNode, VOFinalDiff, VOFinalIntersec, VOFinalUnion, VOInterDiff,
            VOInterIntersec, VOInterUnion, VOKeywordNode, VONode, VORangeNode, VoDag, VO,
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
use smol_str::SmolStr;
use std::collections::{BTreeMap, HashMap};

#[derive(Clone, Debug, Eq, PartialEq)]
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

#[allow(clippy::type_complexity)]
fn query_final<K: Num, T: ReadInterface<K = K>>(
    chain: &T,
    query_plan: QueryPlan<K>,
    pk: &AccPublicKey,
) -> Result<(HashMap<ObjId, Object<K>>, VO<K>)> {
    let mut vo_dag = Graph::<VONode<K>, bool>::new();
    let qp_outputs = query_plan.outputs;
    let qp_dag = query_plan.dag;
    let mut qp_inputs = match toposort(&qp_dag, None) {
        Ok(v) => v,
        Err(_) => {
            bail!("Input query plan graph not valid")
        }
    };
    qp_inputs.reverse();
    let qp_end_blk_height = query_plan.end_blk_height;

    let mut idx_map = HashMap::<NodeIndex, NodeIndex>::new();
    let mut set_map = HashMap::<NodeIndex, Set>::new();
    let mut trie_ctxes = HashMap::<Height, trie_tree::read::ReadContext<T>>::new();
    let mut trie_proofs = HashMap::<Height, trie_tree::proof::Proof>::new();
    let qp_trie_proofs = query_plan.trie_proofs;
    let mut obj_map = HashMap::<ObjId, Object<K>>::new();
    let mut time_win_map = HashMap::<Height, u64>::new();
    let mut merkle_proofs = HashMap::<Height, MerkleProof>::new();

    for idx in qp_inputs {
        if let Some(node) = qp_dag.node_weight(idx) {
            match node {
                QPNode::Range(n) => {
                    time_win_map.insert(n.blk_height, n.time_win);
                    let set;
                    let acc;
                    let proof;
                    if let Some((s, a, p)) = n.set.clone() {
                        set = s;
                        acc = a;
                        proof = p;
                    } else {
                        let bplus_root = chain
                            .read_block_content(n.blk_height)?
                            .ads
                            .read_bplus_root(n.time_win, n.dim)?;
                        let (s, a, p) = bplus_tree::read::range_query(
                            chain,
                            bplus_root.bplus_tree_root_id,
                            n.range,
                            pk,
                        )?;
                        set = s;
                        acc = a;
                        proof = p;
                    }

                    let vo_range_node = VORangeNode {
                        range: n.range,
                        blk_height: n.blk_height,
                        time_win: n.time_win,
                        dim: n.dim,
                        acc,
                        proof,
                    };
                    let vo_idx = vo_dag.add_node(VONode::Range(vo_range_node));
                    idx_map.insert(idx, vo_idx);
                    set_map.insert(vo_idx, set);
                }
                QPNode::Keyword(n) => {
                    time_win_map.insert(n.blk_height, n.time_win);
                    let set;
                    let acc;
                    if let Some((s, a)) = n.set.clone() {
                        set = s;
                        acc = a;
                    } else if let Some(ctx) = trie_ctxes.get_mut(&n.blk_height) {
                        let trie_ctx = ctx;
                        let (s, a) = trie_ctx.query(&SmolStr::from(&n.keyword), pk)?;
                        set = s;
                        acc = a;
                    } else {
                        let trie_root = chain
                            .read_block_content(n.blk_height)?
                            .ads
                            .read_trie_root(n.time_win)?;
                        let mut trie_ctx =
                            trie_tree::read::ReadContext::new(chain, trie_root.trie_root_id);
                        let (s, a) = trie_ctx.query(&SmolStr::from(&n.keyword), pk)?;
                        set = s;
                        acc = a;
                        trie_ctxes.insert(n.blk_height, trie_ctx);
                    }

                    let vo_keyword_node = VOKeywordNode {
                        keyword: n.keyword.clone(),
                        blk_height: n.blk_height,
                        time_win: n.time_win,
                        acc,
                    };
                    let vo_idx = vo_dag.add_node(VONode::Keyword(vo_keyword_node));
                    idx_map.insert(idx, vo_idx);
                    set_map.insert(vo_idx, set);
                }
                QPNode::BlkRt(n) => {
                    time_win_map.insert(n.blk_height, n.time_win);
                    let set;
                    let acc;
                    if let Some((s, a)) = n.set.clone() {
                        set = s;
                        acc = a;
                    } else {
                        let blk_content = chain.read_block_content(Height(n.blk_height.0))?;
                        let bplus_root = blk_content.ads.read_bplus_root(n.time_win, 0)?;
                        let bplus_root_id =
                            bplus_root.bplus_tree_root_id.context("Empty bplus root")?;
                        let bplus_root_node =
                            bplus_tree::BPlusTreeNodeLoader::load_node(chain, bplus_root_id)?;
                        set = bplus_root_node.get_set().clone();
                        acc = bplus_root_node.get_node_acc();
                    }

                    let vo_blk_root = VOBlkRtNode {
                        blk_height: n.blk_height,
                        time_win: n.time_win,
                        acc,
                    };
                    let vo_idx = vo_dag.add_node(VONode::BlkRt(vo_blk_root));
                    idx_map.insert(idx, vo_idx);
                    set_map.insert(vo_idx, set);
                }
                QPNode::Union(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for idx in qp_dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(idx);
                    }
                    let qp_c_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first qp child idx of union")?;
                    let vo_c_idx1 = idx_map
                        .get(qp_c_idx1)
                        .context("Cannot find the first vo node idx of Union in idx_map")?;
                    let vo_c1 = vo_dag
                        .node_weight(*vo_c_idx1)
                        .context("Cannot find the first child vo node in vo_dag")?;
                    let c1_set = set_map
                        .get(vo_c_idx1)
                        .context("Cannot find the set in set_map")?;
                    let qp_c_idx2 = child_idxs
                        .get(0)
                        .context("Cannot find the second qp child idx of union")?;
                    let vo_c_idx2 = idx_map
                        .get(qp_c_idx2)
                        .context("Cannot find the vo node idx of Union in idx_map")?;
                    let vo_c2 = vo_dag
                        .node_weight(*vo_c_idx2)
                        .context("Cannot find the second child vo node in vo_dag")?;
                    let c2_set = set_map
                        .get(vo_c_idx2)
                        .context("Cannot find the set in set_map")?;

                    if !qp_outputs.contains(&idx) {
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
                        let vo_idx = vo_dag.add_node(VONode::InterUnion(vo_inter_union));
                        set_map.insert(vo_idx, res_set);
                        vo_dag.add_edge(vo_idx, *vo_c_idx1, true);
                        vo_dag.add_edge(vo_idx, *vo_c_idx2, false);
                        idx_map.insert(idx, vo_idx);
                    } else {
                        let (res_set, final_proof) =
                            compute_set_operation_final(Op::Union, c1_set, c2_set, pk);
                        let vo_final_union = VOFinalUnion { proof: final_proof };
                        let vo_idx = vo_dag.add_node(VONode::FinalUnion(vo_final_union));
                        set_map.insert(vo_idx, res_set);
                        vo_dag.add_edge(vo_idx, *vo_c_idx1, true);
                        vo_dag.add_edge(vo_idx, *vo_c_idx2, false);
                        idx_map.insert(idx, vo_idx);
                    }
                }
                QPNode::Intersec(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for idx in qp_dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(idx);
                    }
                    let qp_c_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first qp child idx of intersection")?;
                    let vo_c_idx1 = idx_map
                        .get(qp_c_idx1)
                        .context("Cannot find the first vo node idx of Intersec in idx_map")?;
                    let vo_c1 = vo_dag
                        .node_weight(*vo_c_idx1)
                        .context("Cannot find the first child vo node in vo_dag")?;
                    let c1_set = set_map
                        .get(vo_c_idx1)
                        .context("Cannot find the set in set_map")?;
                    let qp_c_idx2 = child_idxs
                        .get(0)
                        .context("Cannot find the second qp child idx of intersection")?;
                    let vo_c_idx2 = idx_map
                        .get(qp_c_idx2)
                        .context("Cannot find the vo node idx of Intersec in idx_map")?;
                    let vo_c2 = vo_dag
                        .node_weight(*vo_c_idx2)
                        .context("Cannot find the second child vo node in vo_dag")?;
                    let c2_set = set_map
                        .get(vo_c_idx2)
                        .context("Cannot find the set in set_map")?;

                    if !qp_outputs.contains(&idx) {
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
                        let vo_idx = vo_dag.add_node(VONode::InterIntersec(vo_inter_intersec));
                        set_map.insert(vo_idx, res_set);
                        vo_dag.add_edge(vo_idx, *vo_c_idx1, true);
                        vo_dag.add_edge(vo_idx, *vo_c_idx2, false);
                        idx_map.insert(idx, vo_idx);
                    } else {
                        let (res_set, final_proof) =
                            compute_set_operation_final(Op::Intersection, c1_set, c2_set, pk);
                        let vo_final_intersec = VOFinalIntersec { proof: final_proof };
                        let vo_idx = vo_dag.add_node(VONode::FinalIntersec(vo_final_intersec));
                        set_map.insert(vo_idx, res_set);
                        vo_dag.add_edge(vo_idx, *vo_c_idx1, true);
                        vo_dag.add_edge(vo_idx, *vo_c_idx2, false);
                        idx_map.insert(idx, vo_idx);
                    }
                }
                QPNode::Diff(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for idx in qp_dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(idx);
                    }

                    let mut qp_c_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first qp child idx of difference")?;
                    let qp_c_idx2;
                    let edge_idx = qp_dag
                        .find_edge(idx, *qp_c_idx1)
                        .context("Cannot find edge")?;
                    let weight = qp_dag.edge_weight(edge_idx).context("Cannot find edge")?;
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

                    let vo_c_idx1 = idx_map
                        .get(qp_c_idx1)
                        .context("Cannot find the first vo node idx of Difference in idx_map")?;
                    let vo_c1 = vo_dag
                        .node_weight(*vo_c_idx1)
                        .context("Cannot find the first child vo node in vo_dag")?;
                    let c1_set = set_map
                        .get(vo_c_idx1)
                        .context("Cannot find the set in set_map")?;

                    let vo_c_idx2 = idx_map
                        .get(qp_c_idx2)
                        .context("Cannot find the vo node idx of Difference in idx_map")?;
                    let vo_c2 = vo_dag
                        .node_weight(*vo_c_idx2)
                        .context("Cannot find the second child vo node in vo_dag")?;
                    let c2_set = set_map
                        .get(vo_c_idx2)
                        .context("Cannot find the set in set_map")?;

                    if !qp_outputs.contains(&idx) {
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
                        let vo_idx = vo_dag.add_node(VONode::InterDiff(vo_inter_diff));
                        set_map.insert(vo_idx, res_set);
                        vo_dag.add_edge(vo_idx, *vo_c_idx1, false);
                        vo_dag.add_edge(vo_idx, *vo_c_idx2, true);
                        idx_map.insert(idx, vo_idx);
                    } else {
                        let (res_set, final_proof) =
                            compute_set_operation_final(Op::Difference, c1_set, c2_set, pk);
                        let vo_final_diff = VOFinalDiff { proof: final_proof };
                        let vo_idx = vo_dag.add_node(VONode::FinalDiff(vo_final_diff));
                        set_map.insert(vo_idx, res_set);
                        vo_dag.add_edge(vo_idx, *vo_c_idx1, false);
                        vo_dag.add_edge(vo_idx, *vo_c_idx2, true);
                        idx_map.insert(idx, vo_idx);
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
    for idx in qp_outputs {
        let vo_idx = idx_map.get(&idx).context("Cannot find idx in idx_map")?;
        let set = set_map
            .remove(vo_idx)
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
        vo_ouput_sets.insert(*vo_idx, sub_res_set);
    }
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
    let vo_dag_struct = VoDag {
        output_sets: vo_ouput_sets,
        dag: vo_dag,
    };
    let vo = VO {
        vo_dag: vo_dag_struct,
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
) -> Result<Vec<(TimeWin, Option<u64>, u64)>> {
    let mut res = Vec::<(TimeWin, Option<u64>, u64)>::new();
    let mut cur_win = query_time_win;
    let min = win_sizes.first().context("Empty time win size")?;
    for win_size in win_sizes.iter().rev() {
        while cur_win.get_end() + 1 >= win_size + cur_win.get_start() {
            let new_time_win =
                TimeWin::new(cur_win.get_start(), cur_win.get_start() + win_size - 1);
            res.push((new_time_win, None, *win_size));
            if cur_win.get_start() + *win_size == cur_win.get_end() + 1 {
                return Ok(res);
            } else {
                cur_win = TimeWin::new(cur_win.get_start() + *win_size, cur_win.get_end());
            }
        }
    }

    res.push((cur_win, Some(*min), *min));
    Ok(res)
}

#[allow(clippy::type_complexity)]
pub fn query<K: Num, T: ReadInterface<K = K> + ScanQueryInterface<K = K>>(
    opt_level: u8,
    chain: T,
    query_param: QueryParam<K>,
    pk: &AccPublicKey,
) -> Result<(Vec<(HashMap<ObjId, Object<K>>, VO<K>)>, QueryTime)> {
    let chain_param = &chain.get_parameter()?;
    let chain_win_sizes = &chain_param.time_win_sizes;
    let mut result = Vec::<(HashMap<ObjId, Object<K>>, VO<K>)>::new();
    let mut stage1_time = Vec::<ProcessDuration>::new();
    let mut stage2_time = Vec::<ProcessDuration>::new();
    let mut stage3_time = Vec::<ProcessDuration>::new();
    let timer = howlong::ProcessCPUTimer::new();
    let query_time_win = query_param.gen_time_win();
    let query_content = query_param.gen_query_content();
    let query_time_wins = select_win_size(chain_win_sizes, query_time_win)?;
    let time = timer.elapsed();
    debug!("Select time win: {}", time);
    for (time_win, s_win_size, e_win_size) in query_time_wins {
        let sub_timer = howlong::ProcessCPUTimer::new();
        let query = match opt_level {
            0 => param_to_query_basic(time_win, &query_content, s_win_size, e_win_size)?,
            1 => param_to_query_trimmed2(
                time_win,
                &query_content,
                &chain,
                pk,
                s_win_size,
                e_win_size,
            )?,
            _ => bail!("invalid opt level"),
        };
        let time = sub_timer.elapsed();
        debug!("Stage1: {}", time);
        stage1_time.push(time);
        let sub_timer = howlong::ProcessCPUTimer::new();
        let mut query_plan = query_to_qp(query)?;
        let time = sub_timer.elapsed();
        debug!("Stage2: {}", time);
        stage2_time.push(time);
        let sub_timer = howlong::ProcessCPUTimer::new();
        let cost = query_plan.estimate_cost(&chain, pk)?;
        let time = sub_timer.elapsed();
        debug!(
            "cost estimate for the query plan: {}, time elapsed: {}",
            cost, time
        );
        let sub_timer = howlong::ProcessCPUTimer::new();
        let res = query_final(&chain, query_plan, pk)?;
        let time = sub_timer.elapsed();
        debug!("Stage3: {}", time);
        stage3_time.push(time);
        result.push(res);
    }
    let total_query_time = Time::from(timer.elapsed());
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
    let query_time = QueryTime {
        stage1: Time::from(stage1_total_time),
        stage2: Time::from(stage2_total_time),
        stage3: Time::from(stage3_total_time),
        total: total_query_time,
    };

    Ok((result, query_time))
}

#[cfg(test)]
mod tests {
    use super::TimeWin;
    use crate::chain::query::select_win_size;

    #[test]
    fn test_select_win_size2() {
        let query_time_win = TimeWin::new(1, 12);
        let res = select_win_size(&vec![2, 4, 8], query_time_win).unwrap();
        let exp = vec![
            (TimeWin::new(1, 8), None, 8),
            (TimeWin::new(9, 12), None, 4),
        ];
        assert_eq!(res, exp);
        let query_time_win = TimeWin::new(1, 13);
        let res = select_win_size(&vec![2, 4, 8], query_time_win).unwrap();
        let exp = vec![
            (TimeWin::new(1, 8), None, 8),
            (TimeWin::new(9, 12), None, 4),
            (TimeWin::new(13, 13), Some(2), 2),
        ];
        assert_eq!(res, exp);
        let query_time_win = TimeWin::new(1, 14);
        let res = select_win_size(&vec![2, 4, 8], query_time_win).unwrap();
        let exp = vec![
            (TimeWin::new(1, 8), None, 8),
            (TimeWin::new(9, 12), None, 4),
            (TimeWin::new(13, 14), None, 2),
        ];
        assert_eq!(res, exp);
    }
}
