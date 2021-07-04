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
use petgraph::{graph::NodeIndex, EdgeDirection::Outgoing, Graph};
use query_param::QueryParam;
use query_plan::QueryPlan;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap};
use std::iter::FromIterator;

#[allow(clippy::type_complexity)]
fn query_final<K: Num, T: ReadInterface<K = K>>(
    chain: T,
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
                                &chain,
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
                                    &chain,
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
    let mut id_tree_ctx = id_tree::read::ReadContext::new(&chain, id_root.get_id_tree_root_id());
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

#[derive(Debug, Serialize, Deserialize)]
pub struct QueryTime {
    pub(crate) param_to_q: Time,
    pub(crate) q_to_qp: Time,
    pub(crate) process_qp: Time,
}

#[allow(clippy::type_complexity)]
pub fn query<K: Num, T: ReadInterface<K = K>>(
    chain: T,
    query_param: QueryParam<K>,
    pk: &AccPublicKey,
) -> Result<((HashMap<ObjId, Object<K>>, VO<K>), QueryTime)> {
    let timer = howlong::ProcessCPUTimer::new();
    let chain_param = chain.get_parameter()?;
    // todo choose proper time_window
    let time_win = *chain_param
        .time_win_sizes
        .get(0)
        .context("No time window provided in this blockchain")?;

    let query = query_param.into_query_basic(time_win)?;
    let time1 = timer.elapsed();
    let timer = howlong::ProcessCPUTimer::new();
    let query_plan = query_to_qp(query)?;
    let time2 = timer.elapsed();
    let timer = howlong::ProcessCPUTimer::new();
    let res = query_final(chain, query_plan, pk)?;
    let time3 = timer.elapsed();
    let time = QueryTime {
        param_to_q: Time::from(time1),
        q_to_qp: Time::from(time2),
        process_qp: Time::from(time3),
    };
    info!("Stage1: {}", time1);
    info!("Stage2: {}", time2);
    info!("Stage3: {}", time3);
    Ok((res, time))
}
