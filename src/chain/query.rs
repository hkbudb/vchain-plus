pub mod query_obj;
pub mod query_param;
pub mod query_plan;

use crate::{
    acc::{
        compute_set_operation_final, compute_set_operation_intermediate, ops::Op, AccPublicKey, Set,
    },
    chain::{
        block::{hash::obj_id_nums_hash, Height},
        bplus_tree,
        id_tree::{self, ObjId},
        object::Object,
        query::{query_obj::query_to_qp, query_plan::QPNode},
        traits::{Num, ReadInterface},
        trie_tree,
        verify::vo::{
            MerkleProof, VOBlkRtNode, VOFinalDiff, VOFinalIntersec, VOFinalUnion, VOInterDiff,
            VOInterIntersec, VOInterUnion, VOKeywordNode, VONode, VORangeNode, VoDag, VO,
        },
    },
    digest::{Digest, Digestible},
    utils::Time,
};
use anyhow::{Context, Result};
use petgraph::dot::{Config, Dot};
use petgraph::{graph::NodeIndex, EdgeDirection::Outgoing, Graph};
use query_param::QueryParam;
use query_plan::QueryPlan;
use std::collections::{BTreeMap, HashMap};
use std::iter::FromIterator;

#[allow(clippy::type_complexity)]
fn query_final<K: Num, T: ReadInterface<K = K>>(
    chain: &T,
    query_plan: QueryPlan<K>,
    pk: &AccPublicKey,
) -> Result<(HashMap<ObjId, Object<K>>, VO<K>)> {
    let mut vo_dag = Graph::<VONode<K>, ()>::new();
    let qp_inputs = query_plan.inputs;
    let qp_outputs = query_plan.outputs;
    let qp_dag = query_plan.dag;
    let qp_trie_proofs = query_plan.trie_proofs;
    let qp_bplus_proofs = query_plan.bplus_proofs;
    let qp_end_blk_height = query_plan.end_blk_height;

    let mut idx_map = HashMap::<NodeIndex, NodeIndex>::new();
    let mut set_map = HashMap::<NodeIndex, Set>::new();
    let mut trie_ctxes = HashMap::<Height, trie_tree::read::ReadContext<T>>::new();
    let mut trie_proofs = HashMap::<Height, trie_tree::proof::Proof>::new();
    let mut obj_map = HashMap::<ObjId, Object<K>>::new();
    let mut time_win_map = HashMap::<Height, u64>::new();
    let mut merkle_proofs = HashMap::<Height, MerkleProof>::new();

    for (h, p) in qp_trie_proofs.into_iter() {
        trie_proofs.insert(h, p);
    }
    for idx in qp_inputs {
        if let Some(node) = qp_dag.node_weight(idx) {
            match node {
                QPNode::Range(n) => {
                    time_win_map.insert(n.blk_height, n.time_win);
                    match &n.set {
                        Some((set, acc)) => {
                            let proofs = qp_bplus_proofs.get(&n.blk_height).context(format!(
                                "Cannot find the bplus tree proof map at height {:?}",
                                n.blk_height
                            ))?;
                            let bplus_p = proofs.get(&n.dim).context(format!(
                                "Cannot find the bplus tree proof at dim {}, height {}",
                                n.dim, n.blk_height
                            ))?;
                            let vo_range_node = VORangeNode {
                                range: n.range,
                                blk_height: n.blk_height,
                                time_win: n.time_win,
                                dim: n.dim,
                                acc: *acc,
                                proof: bplus_p.clone(),
                            };
                            let vo_idx = vo_dag.add_node(VONode::Range(vo_range_node));
                            idx_map.insert(idx, vo_idx);
                            set_map.insert(vo_idx, set.clone());
                        }
                        None => {
                            let bplus_root = chain
                                .read_block_content(n.blk_height)?
                                .ads
                                .read_bplus_root(n.time_win, n.dim)?;
                            let (set, acc, proof) = bplus_tree::read::range_query(
                                chain,
                                bplus_root.bplus_tree_root_id,
                                n.range,
                                pk,
                            )?;
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
                            set_map.insert(vo_idx, set.clone());
                        }
                    }
                }
                QPNode::Keyword(n) => {
                    time_win_map.insert(n.blk_height, n.time_win);
                    match &n.set {
                        Some((s, a)) => {
                            let vo_keyword_node = VOKeywordNode {
                                keyword: n.keyword.clone(),
                                blk_height: n.blk_height,
                                time_win: n.time_win,
                                acc: *a,
                            };
                            let vo_idx = vo_dag.add_node(VONode::Keyword(vo_keyword_node));
                            idx_map.insert(idx, vo_idx);
                            set_map.insert(vo_idx, s.clone());
                        }
                        None => {
                            let set;
                            let acc;
                            if let Some(ctx) = trie_ctxes.get_mut(&n.blk_height) {
                                let trie_ctx = ctx;
                                let (s, a) = trie_ctx.query(n.keyword.clone(), pk)?;
                                set = s;
                                acc = a;
                            } else {
                                let trie_root = chain
                                    .read_block_content(n.blk_height)?
                                    .ads
                                    .read_trie_root(n.time_win)?;
                                let mut trie_ctx = trie_tree::read::ReadContext::new(
                                    chain,
                                    trie_root.trie_root_id,
                                );
                                let (s, a) = trie_ctx.query(n.keyword.clone(), pk)?;
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
                            set_map.insert(vo_idx, set.clone());
                        }
                    }
                }
                QPNode::BlkRt(n) => match &n.set {
                    Some(set) => {
                        let acc;
                        match n.acc {
                            Some(acc_val) => {
                                acc = acc_val;
                            }
                            None => {
                                let blk_content = chain.read_block_content(n.blk_height)?;
                                acc = blk_content
                                    .read_acc()
                                    .context("The block does not have acc value")?;
                            }
                        }
                        let vo_blk_rt_node = VOBlkRtNode {
                            blk_height: n.blk_height,
                            acc,
                        };
                        let vo_idx = vo_dag.add_node(VONode::BlkRt(vo_blk_rt_node));
                        idx_map.insert(idx, vo_idx);
                        set_map.insert(vo_idx, set.clone());
                    }
                    None => {
                        let blk_content = chain.read_block_content(n.blk_height)?;
                        let obj_id_nums = blk_content.read_obj_id_nums();
                        let set = Set::from_iter(obj_id_nums.into_iter());
                        let acc = blk_content
                            .read_acc()
                            .context("The block does not have acc value")?;
                        let vo_blk_root = VOBlkRtNode {
                            blk_height: n.blk_height,
                            acc,
                        };
                        let vo_idx = vo_dag.add_node(VONode::BlkRt(vo_blk_root));
                        idx_map.insert(idx, vo_idx);
                        set_map.insert(vo_idx, set);
                    }
                },
                QPNode::Union(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for idx in qp_dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(idx);
                    }
                    let qp_c_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first qp child idx of union")?;
                    let vo_c_idx1 = idx_map
                        .get(&qp_c_idx1)
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
                        .get(&qp_c_idx2)
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
                        vo_dag.add_edge(vo_idx, *vo_c_idx1, ());
                        vo_dag.add_edge(vo_idx, *vo_c_idx2, ());
                        idx_map.insert(idx, vo_idx);
                    } else {
                        let (res_set, final_proof) =
                            compute_set_operation_final(Op::Union, c1_set, c2_set, pk);
                        let vo_final_union = VOFinalUnion { proof: final_proof };
                        let vo_idx = vo_dag.add_node(VONode::FinalUnion(vo_final_union));
                        set_map.insert(vo_idx, res_set);
                        vo_dag.add_edge(vo_idx, *vo_c_idx1, ());
                        vo_dag.add_edge(vo_idx, *vo_c_idx2, ());
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
                        .get(&qp_c_idx1)
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
                        .get(&qp_c_idx2)
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
                        vo_dag.add_edge(vo_idx, *vo_c_idx1, ());
                        vo_dag.add_edge(vo_idx, *vo_c_idx2, ());
                        idx_map.insert(idx, vo_idx);
                    } else {
                        let (res_set, final_proof) =
                            compute_set_operation_final(Op::Intersection, c1_set, c2_set, pk);
                        let vo_final_intersec = VOFinalIntersec { proof: final_proof };
                        let vo_idx = vo_dag.add_node(VONode::FinalIntersec(vo_final_intersec));
                        set_map.insert(vo_idx, res_set);
                        vo_dag.add_edge(vo_idx, *vo_c_idx1, ());
                        vo_dag.add_edge(vo_idx, *vo_c_idx2, ());
                        idx_map.insert(idx, vo_idx);
                    }
                }
                QPNode::Diff(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for idx in qp_dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(idx);
                    }
                    let qp_c_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first qp child idx of difference")?;
                    let vo_c_idx1 = idx_map
                        .get(&qp_c_idx1)
                        .context("Cannot find the first vo node idx of Difference in idx_map")?;
                    let vo_c1 = vo_dag
                        .node_weight(*vo_c_idx1)
                        .context("Cannot find the first child vo node in vo_dag")?;
                    let c1_set = set_map
                        .get(vo_c_idx1)
                        .context("Cannot find the set in set_map")?;

                    let qp_c_idx2 = child_idxs
                        .get(0)
                        .context("Cannot second the first qp child idx of difference")?;
                    let vo_c_idx2 = idx_map
                        .get(&qp_c_idx2)
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
                        vo_dag.add_edge(vo_idx, *vo_c_idx1, ());
                        vo_dag.add_edge(vo_idx, *vo_c_idx2, ());
                        idx_map.insert(idx, vo_idx);
                    } else {
                        let (res_set, final_proof) =
                            compute_set_operation_final(Op::Difference, c1_set, c2_set, pk);
                        let vo_final_diff = VOFinalDiff { proof: final_proof };
                        let vo_idx = vo_dag.add_node(VONode::FinalDiff(vo_final_diff));
                        set_map.insert(vo_idx, res_set);
                        vo_dag.add_edge(vo_idx, *vo_c_idx1, ());
                        vo_dag.add_edge(vo_idx, *vo_c_idx2, ());
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

    let id_root = chain.read_block_content(qp_end_blk_height)?.id_tree_root;
    let cur_obj_id = id_root.get_cur_obj_id();
    let mut id_tree_ctx = id_tree::read::ReadContext::new(chain, id_root.get_id_tree_root_id());
    let param = chain.get_parameter()?;
    let max_id_num = param.max_id_num;
    let id_tree_fanout = param.id_tree_fanout;
    let mut vo_ouput_sets = HashMap::<NodeIndex, Set>::new();
    for idx in qp_outputs {
        let vo_idx = idx_map.get(&idx).context("Cannot find idx in idx_map")?;
        let set = set_map.get(vo_idx).context("Cannot find set in set_map")?;
        vo_ouput_sets.insert(*vo_idx, set.clone());
        for i in set.iter() {
            let obj_id = ObjId(*i);
            let obj_hash = id_tree_ctx
                .query(obj_id, max_id_num, id_tree_fanout)?
                .context("Cannot find object")?;
            let obj = chain.read_object(obj_hash)?;
            obj_map.insert(obj_id, obj);
        }
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
fn select_win_size<K: Num>(
    mut win_sizes: Vec<u64>,
    query_param: QueryParam<K>,
) -> Result<Vec<(QueryParam<K>, Option<u64>, u64)>> {
    let mut res = Vec::<(QueryParam<K>, Option<u64>, u64)>::new();
    win_sizes.sort_unstable();
    let mut cur_param = query_param;
    let max = *win_sizes.last().context("No time window")?;
    while cur_param.get_end() + 1 >= max + cur_param.get_start() {
        let new_param =
            cur_param.copy_on_write(cur_param.get_start(), cur_param.get_start() + max - 1);
        res.push((new_param, None, max));
        if cur_param.get_start() + max > cur_param.get_end() {
            cur_param =
                cur_param.copy_on_write(cur_param.get_start() + max - 1, cur_param.get_end());
            if cur_param.get_end() == cur_param.get_start() {
                return Ok(res);
            }
        } else {
            cur_param = cur_param.copy_on_write(cur_param.get_start() + max, cur_param.get_end());
        }
    }
    let cur_size = cur_param.get_end() - cur_param.get_start();

    let mut idx = 0;
    for (i, win_size) in win_sizes.iter().enumerate() {
        if cur_size < *win_size {
            idx = i;
            break;
        }
    }
    let higher = win_sizes.get(idx).context("Cannot find size")?;
    let mut start_idx = 0;
    let mut lower = *win_sizes.get(start_idx).context("No time window")?;
    while cur_param.get_start() > lower
        && cur_param.get_start() + higher > cur_param.get_end() + lower
    {
        start_idx += 1;
        lower = *win_sizes.get(start_idx).context("No time window")?;
    }
    res.push((cur_param, Some(lower), *higher));
    Ok(res)
}

#[allow(clippy::type_complexity)]
pub fn query<K: Num, T: ReadInterface<K = K>>(
    chain: T,
    query_param: QueryParam<K>,
    pk: &AccPublicKey,
) -> Result<(Vec<(HashMap<ObjId, Object<K>>, VO<K>)>, Time)> {
    let timer = howlong::ProcessCPUTimer::new();
    let chain_param = &chain.get_parameter()?;
    let chain_win_sizes = chain_param.time_win_sizes.clone();
    let query_params = select_win_size(chain_win_sizes, query_param)?;
    let mut result = Vec::<(HashMap<ObjId, Object<K>>, VO<K>)>::new();
    for (q_param, s_win_size, e_win_size) in query_params {
        let sub_timer = howlong::ProcessCPUTimer::new();
        let query = q_param.into_query_basic(s_win_size, e_win_size)?;
        debug!(
            "query dag: {:?}",
            Dot::with_config(&query.query_dag, &[Config::EdgeNoLabel])
        );
        let time = sub_timer.elapsed();
        debug!("Stage1: {}", time);
        let sub_timer = howlong::ProcessCPUTimer::new();
        let query_plan = query_to_qp(query)?;
        debug!(
            "query plan dag: {:?}",
            Dot::with_config(&query_plan.dag, &[Config::EdgeNoLabel])
        );
        let time = sub_timer.elapsed();
        debug!("Stage2: {}", time);
        let sub_timer = howlong::ProcessCPUTimer::new();
        let res = query_final(&chain, query_plan, pk)?;
        let time = sub_timer.elapsed();
        debug!("Stage3: {}", time);
        result.push(res);
    }
    let total_query_time = Time::from(timer.elapsed());
    Ok((result, total_query_time))
}

#[cfg(test)]
mod tests {
    use crate::chain::query::{
        query_param::{Node, QueryParam},
        select_win_size,
    };

    #[test]
    fn test_select_win_size() {
        let query_param = QueryParam::<u32> {
            start_blk: 1,
            end_blk: 3,
            range: vec![],
            keyword_exp: Node::Input("a".to_string()),
        };
        let res = select_win_size(vec![4], query_param.clone()).unwrap();
        let exp = vec![(query_param, Some(4), 4)];
        assert_eq!(res, exp);
        let query_param = QueryParam::<u32> {
            start_blk: 1,
            end_blk: 4,
            range: vec![],
            keyword_exp: Node::Input("a".to_string()),
        };
        let res = select_win_size(vec![4], query_param.clone()).unwrap();
        let exp = vec![(query_param, None, 4)];
        assert_eq!(res, exp);
        let query_param = QueryParam::<u32> {
            start_blk: 1,
            end_blk: 5,
            range: vec![],
            keyword_exp: Node::Input("a".to_string()),
        };
        let res = select_win_size(vec![4], query_param).unwrap();
        let exp = vec![
            (
                QueryParam::<u32> {
                    start_blk: 1,
                    end_blk: 4,
                    range: vec![],
                    keyword_exp: Node::Input("a".to_string()),
                },
                None,
                4,
            ),
            (
                QueryParam::<u32> {
                    start_blk: 5,
                    end_blk: 5,
                    range: vec![],
                    keyword_exp: Node::Input("a".to_string()),
                },
                Some(4),
                4,
            ),
        ];
        assert_eq!(res, exp);
        let query_param = QueryParam::<u32> {
            start_blk: 1,
            end_blk: 6,
            range: vec![],
            keyword_exp: Node::Input("a".to_string()),
        };
        let res = select_win_size(vec![4, 8], query_param.clone()).unwrap();
        let exp = vec![(query_param, Some(4), 8)];
        assert_eq!(res, exp);
        let query_param = QueryParam::<u32> {
            start_blk: 1,
            end_blk: 8,
            range: vec![],
            keyword_exp: Node::Input("a".to_string()),
        };
        let res = select_win_size(vec![4, 8], query_param.clone()).unwrap();
        let exp = vec![(query_param, None, 8)];
        assert_eq!(res, exp);
        let query_param = QueryParam::<u32> {
            start_blk: 1,
            end_blk: 10,
            range: vec![],
            keyword_exp: Node::Input("a".to_string()),
        };
        let res = select_win_size(vec![4, 8], query_param).unwrap();
        let exp = vec![
            (
                QueryParam::<u32> {
                    start_blk: 1,
                    end_blk: 8,
                    range: vec![],
                    keyword_exp: Node::Input("a".to_string()),
                },
                None,
                8,
            ),
            (
                QueryParam::<u32> {
                    start_blk: 9,
                    end_blk: 10,
                    range: vec![],
                    keyword_exp: Node::Input("a".to_string()),
                },
                Some(4),
                4,
            ),
        ];
        assert_eq!(res, exp);
        let query_param = QueryParam::<u32> {
            start_blk: 1,
            end_blk: 16,
            range: vec![],
            keyword_exp: Node::Input("a".to_string()),
        };
        let res = select_win_size(vec![4, 8], query_param).unwrap();
        let exp = vec![
            (
                QueryParam::<u32> {
                    start_blk: 1,
                    end_blk: 8,
                    range: vec![],
                    keyword_exp: Node::Input("a".to_string()),
                },
                None,
                8,
            ),
            (
                QueryParam::<u32> {
                    start_blk: 9,
                    end_blk: 16,
                    range: vec![],
                    keyword_exp: Node::Input("a".to_string()),
                },
                None,
                8,
            ),
        ];
        assert_eq!(res, exp);
    }
}
