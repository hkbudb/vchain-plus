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
    pub vo_size: usize,
    pub verify_time: Time,
}

fn inner_verify<K: Num, T: ReadInterface<K = K>>(
    chain: &T,
    res: &HashMap<ObjId, Object<K>>,
    vo: &VO<K>,
    pk: &AccPublicKey,
) -> Result<()> {
    // verify dag, including range query and set operation
    let vo_dag_struct = &vo.vo_dag;
    let vo_dag = &vo_dag_struct.dag;
    let vo_output_sets = &vo_dag_struct.output_sets;
    let vo_dag_idxs = vo_dag.node_indices();
    let mut bplus_roots = HashMap::<Height, (u64, BTreeMap<usize, Digest>)>::new();
    let trie_proofs = &vo.trie_proofs;
    let mut time_win_map = HashMap::<Height, u64>::new();
    for idx in vo_dag_idxs {
        if let Some(node) = vo_dag.node_weight(idx) {
            match node {
                vo::VONode::Range(n) => {
                    time_win_map.insert(n.blk_height, n.time_win);
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
                    time_win_map.insert(n.blk_height, n.time_win);
                    let proof = trie_proofs
                        .get(&n.blk_height)
                        .context("Inside dag: cannot find trie proof in VO")?;
                    proof.verify_acc(n.acc, &n.keyword, pk)?;
                }
                vo::VONode::BlkRt(n) => {
                    time_win_map.insert(n.blk_height, n.time_win);
                }
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
                    let mut child_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first child idx of intermediate difference")?;
                    let child_idx2;
                    let edge_idx = vo_dag
                        .find_edge(idx, *child_idx1)
                        .context("Cannot find edge")?;
                    let weight = vo_dag.edge_weight(edge_idx).context("Cannot find edge")?;
                    if !*weight {
                        child_idx2 = child_idxs.get(0).context(
                            "Cannot find the second child idx of intermediate difference",
                        )?;
                    } else {
                        child_idx1 = child_idxs.get(0).context(
                            "Cannot find the first child idx of intermediate difference",
                        )?;
                        child_idx2 = child_idxs.get(1).context(
                            "Cannot find the second child idx of intermediate difference",
                        )?;
                    }
                    let child1 = vo_dag
                        .node_weight(*child_idx1)
                        .context("Cannot find the second child node in vo_dag")?;
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
                    let mut child_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first child idx of intermediate difference")?;
                    let child_idx2;
                    let edge_idx = vo_dag
                        .find_edge(idx, *child_idx1)
                        .context("Cannot find edge")?;
                    let weight = vo_dag.edge_weight(edge_idx).context("Cannot find edge")?;
                    if !*weight {
                        child_idx2 = child_idxs.get(0).context(
                            "Cannot find the second child idx of intermediate difference",
                        )?;
                    } else {
                        child_idx1 = child_idxs.get(0).context(
                            "Cannot find the first child idx of intermediate difference",
                        )?;
                        child_idx2 = child_idxs.get(1).context(
                            "Cannot find the second child idx of intermediate difference",
                        )?;
                    }
                    let child1 = vo_dag
                        .node_weight(*child_idx1)
                        .context("Cannot find the second child node in vo_dag")?;
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
    let id_tree_proof = &vo.id_tree_proof;
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
    let merkle_proofs = &vo.merkle_proofs;
    for (height, time_win) in time_win_map {
        if let Some((_win_size, bplus_hashes)) = bplus_roots.get(&height) {
            let bplus_root_hash = bplus_roots_hash(bplus_hashes.iter());
            let trie_proof = trie_proofs.get(&height).context("Cannot find trie proof")?;
            let hash = ads_hash(bplus_root_hash, trie_proof.root_hash());
            let merkle_proof = merkle_proofs
                .get(&height)
                .context("Cannot find merkle proof")?;
            let id_root_hash = match merkle_proof.id_tree_root_hash {
                Some(d) => d,
                None => id_tree_root_hash,
            };
            let ads_root_hash =
                merkle_proof.ads_root_hash(&id_root_hash, std::iter::once((time_win, hash)));
            let expect_ads_root_hash = chain.read_block_head(height)?.get_ads_root_hash();
            ensure!(
                ads_root_hash == expect_ads_root_hash,
                "ADS root hash not matched for height {:?}!. The target hash is {:?} but the computed hash is {:?}", height, expect_ads_root_hash, ads_root_hash
            );
        }
    }

    Ok(())
}

fn cal_vo_size<K: Num + Serialize>(vo: &VO<K>) -> Result<usize> {
    info!("VO size profile: ");
    info!("VO dag size: {}", bincode::serialize(&vo.vo_dag)?.len());
    info!("trie_proofs size: {}", bincode::serialize(&vo.trie_proofs)?.len());
    info!("id_tree_proof size: {}", bincode::serialize(&vo.id_tree_proof)?.len());
    info!("cur_obj_id size: {}", bincode::serialize(&vo.cur_obj_id)?.len());
    info!("merkle_proofs size: {}", bincode::serialize(&vo.merkle_proofs)?.len());
    Ok(bincode::serialize(vo)?.len())
}

#[allow(clippy::type_complexity)]
pub fn verify<K: Num + Serialize, T: ReadInterface<K = K>>(
    chain: T,
    res: Vec<(HashMap<ObjId, Object<K>>, VO<K>)>,
    pk: &AccPublicKey,
) -> Result<VerifyInfo> {
    let timer = howlong::ProcessCPUTimer::new();
    let mut obj_num = 0;
    for (res, vo) in &res {
        inner_verify(&chain, res, vo, pk)?;
        obj_num += res.len();
        debug!("{:?}", res);
    }
    let time = Time::from(timer.elapsed());
    info!("Total number of result object returned: {}", obj_num);

    let mut total_vo_size = 0;
    for (_, vo) in &res {
        total_vo_size += cal_vo_size(vo)?;
    }

    Ok(VerifyInfo {
        vo_size: total_vo_size,
        verify_time: time,
    })
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
