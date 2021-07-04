pub mod hash;
pub mod vo;

use crate::{
    acc::AccPublicKey,
    chain::{
        traits::Num,
        {block::Height, id_tree::ObjId, object::Object, traits::ReadInterface},
    },
    digest::{Digest, Digestible},
    utils::Time,
};
use anyhow::{ensure, Context, Result};
use hash::{ads_hash, bplus_roots_hash};
use hash::{id_tree_root_hash, obj_hash};
use petgraph::{graph::NodeIndex, EdgeDirection::Outgoing};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap};
use vo::VO;

#[derive(Debug, Serialize, Deserialize)]
pub struct VerifyInfo {
    vo_size: usize,
    verify_time: Time,
}

pub fn verify<K: Num, T: ReadInterface<K = K>>(
    chain: T,
    res: &HashMap<ObjId, Object<K>>,
    vo: VO<K>,
    pk: &AccPublicKey,
) -> Result<VerifyInfo> {
    // verify dag, including range query and set operation
    let bytes = bincode::serialize(&vo)?;
    let vo_size = bytes.len();
    let timer = howlong::ProcessCPUTimer::new();
    let vo_dag_struct = vo.vo_dag;
    let vo_dag = vo_dag_struct.dag;
    let vo_output_sets = vo_dag_struct.output_sets;
    let vo_dag_idxs = vo_dag.node_indices();
    let mut bplus_roots = HashMap::<Height, (u64, BTreeMap<usize, Digest>)>::new();
    let trie_proofs = vo.trie_proofs;
    for idx in vo_dag_idxs {
        if let Some(node) = vo_dag.node_weight(idx) {
            match node {
                vo::VONode::Range(n) => {
                    let res_digest = n.proof.verify(n.range, n.acc, pk)?;

                    match bplus_roots.get_mut(&n.blk_height) {
                        Some((_time_win, btree_map)) => {
                            btree_map.insert(n.dim, res_digest);
                        }
                        None => {
                            let mut btree_map = BTreeMap::<usize, Digest>::new();
                            btree_map.insert(n.dim, res_digest);
                            bplus_roots.insert(n.blk_height, (n.time_win, btree_map));
                        }
                    }
                }
                vo::VONode::Keyword(n) => {
                    let proof = trie_proofs
                        .get(&n.blk_height)
                        .context("Cannot find trie proof in VO")?;
                    proof.verify_acc(n.acc, n.keyword.clone(), pk)?;
                }
                vo::VONode::BlkRt(_) => {}
                vo::VONode::InterUnion(n) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for idx in vo_dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(idx);
                    }
                    let child_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first child idx of intermediate union")?;
                    let child1 = vo_dag
                        .node_weight(*child_idx1)
                        .context("Cannot find the second child node in vo_dag")?;
                    let child_idx2 = child_idxs
                        .get(0)
                        .context("Cannot find the second child idx of intermediate union")?;
                    let child2 = vo_dag
                        .node_weight(*child_idx2)
                        .context("Cannot find the second child node in vo_dag")?;
                    n.proof
                        .verify(child1.get_acc()?, child2.get_acc()?, &n.acc, pk)?;
                }
                vo::VONode::FinalUnion(n) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for idx in vo_dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(idx);
                    }
                    let child_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first child idx of final union")?;
                    let child1 = vo_dag
                        .node_weight(*child_idx1)
                        .context("Cannot find the second child node in vo_dag")?;
                    let child_idx2 = child_idxs
                        .get(0)
                        .context("Cannot find the second child idx of final union")?;
                    let child2 = vo_dag
                        .node_weight(*child_idx2)
                        .context("Cannot find the second child node in vo_dag")?;
                    let final_set = vo_output_sets
                        .get(&idx)
                        .context("Cannot find set in VO output sets")?;
                    n.proof
                        .verify(child1.get_acc()?, child2.get_acc()?, final_set, pk)?;
                }
                vo::VONode::InterIntersec(n) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for idx in vo_dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(idx);
                    }
                    let child_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first child idx of intermediate intersection")?;
                    let child1 = vo_dag
                        .node_weight(*child_idx1)
                        .context("Cannot find the second child node in vo_dag")?;
                    let child_idx2 = child_idxs
                        .get(0)
                        .context("Cannot find the second child idx of intermediate intersection")?;
                    let child2 = vo_dag
                        .node_weight(*child_idx2)
                        .context("Cannot find the second child node in vo_dag")?;
                    n.proof
                        .verify(child1.get_acc()?, child2.get_acc()?, &n.acc, pk)?;
                }
                vo::VONode::FinalIntersec(n) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for idx in vo_dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(idx);
                    }
                    let child_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first child idx of final intersection")?;
                    let child1 = vo_dag
                        .node_weight(*child_idx1)
                        .context("Cannot find the second child node in vo_dag")?;
                    let child_idx2 = child_idxs
                        .get(0)
                        .context("Cannot find the second child idx of final intersection")?;
                    let child2 = vo_dag
                        .node_weight(*child_idx2)
                        .context("Cannot find the second child node in vo_dag")?;
                    let final_set = vo_output_sets
                        .get(&idx)
                        .context("Cannot find set in VO output sets")?;
                    n.proof
                        .verify(child1.get_acc()?, child2.get_acc()?, final_set, pk)?;
                }
                vo::VONode::InterDiff(n) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for idx in vo_dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(idx);
                    }
                    let child_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first child idx of intermediate difference")?;
                    let child1 = vo_dag
                        .node_weight(*child_idx1)
                        .context("Cannot find the second child node in vo_dag")?;
                    let child_idx2 = child_idxs
                        .get(0)
                        .context("Cannot find the second child idx of intermediate difference")?;
                    let child2 = vo_dag
                        .node_weight(*child_idx2)
                        .context("Cannot find the second child node in vo_dag")?;
                    n.proof
                        .verify(child1.get_acc()?, child2.get_acc()?, &n.acc, pk)?;
                }
                vo::VONode::FinalDiff(n) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for idx in vo_dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(idx);
                    }
                    let child_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first child idx of final difference")?;
                    let child1 = vo_dag
                        .node_weight(*child_idx1)
                        .context("Cannot find the second child node in vo_dag")?;
                    let child_idx2 = child_idxs
                        .get(0)
                        .context("Cannot find the second child idx of final difference")?;
                    let child2 = vo_dag
                        .node_weight(*child_idx2)
                        .context("Cannot find the second child node in vo_dag")?;
                    let final_set = vo_output_sets
                        .get(&idx)
                        .context("Cannot find set in VO output sets")?;
                    n.proof
                        .verify(child1.get_acc()?, child2.get_acc()?, final_set, pk)?;
                }
            }
        }
    }

    // verify id tree
    let id_tree_proof = vo.id_tree_proof;
    let param = chain.get_parameter()?;
    let max_id_num = param.max_id_num;
    let id_tree_fanout = param.id_tree_fanout;
    for (id, obj) in res {
        let target_hash = obj_hash(obj, id);
        id_tree_proof.verify_value(target_hash, *id, max_id_num, id_tree_fanout)?;
    }
    let id_tree_root_node_hash = id_tree_proof.root_hash();
    let id_tree_root_hash = id_tree_root_hash(vo.cur_obj_id.to_digest(), id_tree_root_node_hash);

    // verify merkle proof, including trie and block head hash
    let mut merkle_proofs = vo.merkle_proofs;
    for (height, (time_win, bplus_hashes)) in bplus_roots {
        let bplus_root_hash = bplus_roots_hash(bplus_hashes.into_iter());
        let trie_proof = trie_proofs.get(&height).context("Cannot find trie proof")?;
        let hash = ads_hash(bplus_root_hash, trie_proof.root_hash());
        let merkle_proof = merkle_proofs
            .get_mut(&height)
            .context("Cannot find merkle proof")?;
        merkle_proof.insert_ads_hash(time_win, hash);
        let id_root_hash = match merkle_proof.id_tree_root_hash {
            Some(d) => d,
            None => id_tree_root_hash,
        };
        let ads_root_hash = merkle_proof.ads_root_hash(&id_root_hash);
        let expect_ads_root_hash = chain.read_block_head(height)?.get_ads_root_hash();
        ensure!(
            ads_root_hash == expect_ads_root_hash,
            "ADS root hash not matched for height {:?}!. The target hash is {:?} but the computed hash is {:?}", height, expect_ads_root_hash, ads_root_hash
        );
    }
    let time = timer.elapsed();
    let verify_time = VerifyInfo {
        vo_size,
        verify_time: time.into(),
    };
    info!("Verification time: {}", time);
    Ok(verify_time)
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_graph() {
        use petgraph::{EdgeDirection::Outgoing, Graph};
        let mut dag = Graph::<u32, ()>::new();
        let idx1 = dag.add_node(1);
        let idx2 = dag.add_node(2);
        let idx3 = dag.add_node(3);
        let idx4 = dag.add_node(4);
        let idx5 = dag.add_node(5);
        let idx6 = dag.add_node(6);
        dag.extend_with_edges(&[
            (idx1, idx2),
            (idx1, idx3),
            (idx2, idx4),
            (idx2, idx5),
            (idx3, idx5),
            (idx3, idx6),
        ]);

        println!("for idx1's children: ");
        for child_idx in dag.neighbors_directed(idx1, Outgoing) {
            println!("{:?}", child_idx);
        }
        println!("for idx2's children: ");
        for child_idx in dag.neighbors_directed(idx2, Outgoing) {
            println!("{:?}", child_idx);
        }
        println!("for idx3's children: ");
        for child_idx in dag.neighbors_directed(idx3, Outgoing) {
            println!("{:?}", child_idx);
        }
        assert_eq!(1, 1);
    }
}
