use crate::{
    acc::{AccPublicKey, AccValue, Set},
    chain::{
        block::Height,
        bplus_tree,
        query::query_plan::{
            QPBlkRtNode, QPDiff, QPIntersec, QPKeywordNode, QPNode, QPRangeNode, QPUnion, QueryPlan,
        },
        range::Range,
        traits::{Num, ReadInterface},
        trie_tree::{self},
        COST_COEFFICIENT,
    },
};
use anyhow::{bail, Context, Result};
use petgraph::{algo::toposort, graph::NodeIndex, EdgeDirection::Outgoing, Graph};
use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet},
    iter::FromIterator,
    num::NonZeroU64,
};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum QueryNode<K: Num> {
    Range(RangeNode<K>),
    Keyword(Box<KeywordNode>),
    BlkRt(Box<BlkRtNode>),
    Union(UnionNode),
    Intersec(IntersecNode),
    Diff(DiffNode),
}

impl<K: Num> QueryNode<K> {
    pub fn get_set(&self) -> Result<&Set> {
        match self {
            QueryNode::Range(n) => Ok(&n.set.as_ref().context("No set in the QueryNode")?.0),
            QueryNode::Keyword(n) => Ok(&n.set.as_ref().context("No set in the QueryNode")?.0),
            QueryNode::BlkRt(n) => Ok(&n.set.as_ref().context("No set in the QueryNode")?.0),
            QueryNode::Union(n) => Ok(n.set.as_ref().context("No set in the QueryNode")?),
            QueryNode::Intersec(n) => Ok(n.set.as_ref().context("No set in the QueryNode")?),
            QueryNode::Diff(n) => Ok(n.set.as_ref().context("No set in the QueryNode")?),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RangeNode<K: Num> {
    pub(crate) range: Range<K>,
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
    pub(crate) dim: usize,
    pub(crate) set: Option<(Set, AccValue, bplus_tree::proof::Proof<K>)>,
}

impl<K: Num> RangeNode<K> {
    pub fn estimate_size<T: ReadInterface<K = K>>(
        &mut self,
        chain: &T,
        pk: &AccPublicKey,
    ) -> Result<()> {
        if self.set.is_none() {
            let bplus_root = chain
                .read_block_content(self.blk_height)?
                .ads
                .read_bplus_root(self.time_win, self.dim)?;
            let (s, a, p) = bplus_tree::read::range_query(
                chain,
                bplus_root.bplus_tree_root_id,
                self.range,
                pk,
            )?;
            self.set = Some((s, a, p));
        }
        Ok(())
    }
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct KeywordNode {
    pub(crate) keyword: String,
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
    pub(crate) set: Option<(Set, AccValue)>,
}

impl KeywordNode {
    pub fn estimate_size<K: Num, T: ReadInterface<K = K>>(
        &mut self,
        trie_ctx: &mut trie_tree::read::ReadContext<T>,
        pk: &AccPublicKey,
    ) -> Result<()> {
        if self.set.is_none() {
            let keyword = &self.keyword;
            let (s, a) = trie_ctx.query(keyword, pk)?;
            self.set = Some((s, a));
            Ok(())
        } else {
            Ok(())
        }
    }
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct BlkRtNode {
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
    pub(crate) set: Option<(Set, AccValue)>,
}

impl BlkRtNode {
    pub fn estimate_size<K: Num, T: ReadInterface<K = K>>(
        &mut self,
        chain: &T,
        pk: &AccPublicKey,
    ) -> Result<()> {
        if self.set.is_none() {
            let mut a = AccValue::from_set(&Set::new(), pk);
            let mut total_obj_id_nums = Vec::<NonZeroU64>::new();
            for i in 0..self.time_win {
                if self.blk_height.0 > i {
                    let blk_content = chain.read_block_content(Height(self.blk_height.0 - i))?;
                    let mut obj_id_nums = blk_content.read_obj_id_nums();
                    total_obj_id_nums.append(&mut obj_id_nums);
                    let sub_acc = blk_content
                        .read_acc()
                        .context("The block does not have acc value")?;
                    a = a + sub_acc;
                }
            }
            let s = Set::from_iter(total_obj_id_nums.into_iter());
            self.set = Some((s, a));
            Ok(())
        } else {
            Ok(())
        }
    }
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct UnionNode {
    pub(crate) set: Option<Set>,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct IntersecNode {
    pub(crate) set: Option<Set>,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct DiffNode {
    pub(crate) set: Option<Set>,
}

#[derive(Debug)]
pub struct Query<K: Num> {
    pub(crate) end_blk_height: Height,
    pub(crate) query_dag: Graph<QueryNode<K>, bool>,
    pub(crate) trie_proofs: HashMap<Height, trie_tree::proof::Proof>,
}

pub fn query_to_qp<K: Num>(query: Query<K>) -> Result<QueryPlan<K>> {
    let mut qp_dag = Graph::<QPNode<K>, bool>::new();
    let query_dag = query.query_dag;
    let query_end_blk_height = query.end_blk_height;
    let mut q_inputs = match toposort(&query_dag, None) {
        Ok(v) => v,
        Err(_) => {
            bail!("Input query graph not valid")
        }
    };
    q_inputs.reverse();
    let q_output_elm = q_inputs
        .last()
        .cloned()
        .context("Input query graph is empty")?;
    let mut idx_map = HashMap::<NodeIndex, NodeIndex>::new();
    let q_outputs = vec![q_output_elm];
    let mut qp_outputs = HashSet::<NodeIndex>::new();

    for idx in q_inputs {
        if let Some(node) = query_dag.node_weight(idx) {
            match node {
                QueryNode::Range(n) => {
                    let qp_range_node = QPRangeNode {
                        range: n.range,
                        blk_height: n.blk_height,
                        time_win: n.time_win,
                        dim: n.dim,
                        set: n.set.clone(),
                    };
                    let qp_idx = qp_dag.add_node(QPNode::Range(qp_range_node));
                    idx_map.insert(idx, qp_idx);
                }
                QueryNode::Keyword(n) => {
                    let qp_keyword_node = QPKeywordNode {
                        keyword: n.keyword.clone(),
                        blk_height: n.blk_height,
                        time_win: n.time_win,
                        set: n.set.clone(),
                    };
                    let qp_idx = qp_dag.add_node(QPNode::Keyword(Box::new(qp_keyword_node)));
                    idx_map.insert(idx, qp_idx);
                }
                QueryNode::BlkRt(n) => {
                    let qp_blk_rt_node = QPBlkRtNode {
                        blk_height: n.blk_height,
                        time_win: n.time_win,
                        set: n.set.clone(),
                    };
                    let qp_idx = qp_dag.add_node(QPNode::BlkRt(Box::new(qp_blk_rt_node)));
                    idx_map.insert(idx, qp_idx);
                }
                QueryNode::Union(_) => {
                    let qp_union = QPUnion { set: None };
                    let qp_idx = qp_dag.add_node(QPNode::Union(qp_union));
                    idx_map.insert(idx, qp_idx);
                    for child_idx in query_dag.neighbors_directed(idx, Outgoing) {
                        if let Some(target_idx) = idx_map.get(&child_idx) {
                            let edge_idx = query_dag
                                .find_edge(idx, child_idx)
                                .context("Cannot find edge")?;
                            let weight = query_dag
                                .edge_weight(edge_idx)
                                .context("Cannot find edge")?;
                            qp_dag.add_edge(qp_idx, *target_idx, *weight);
                        } else {
                            bail!("Cannot find the child idx of union in idx_map");
                        }
                    }
                }
                QueryNode::Intersec(_) => {
                    let qp_intersec = QPIntersec { set: None };
                    let qp_idx = qp_dag.add_node(QPNode::Intersec(qp_intersec));
                    idx_map.insert(idx, qp_idx);
                    for child_idx in query_dag.neighbors_directed(idx, Outgoing) {
                        if let Some(target_idx) = idx_map.get(&child_idx) {
                            let edge_idx = query_dag
                                .find_edge(idx, child_idx)
                                .context("Cannot find edge")?;
                            let weight = query_dag
                                .edge_weight(edge_idx)
                                .context("Cannot find edge")?;
                            qp_dag.add_edge(qp_idx, *target_idx, *weight);
                        } else {
                            bail!("Cannot find the child idx of intersection in idx_map");
                        }
                    }
                }
                QueryNode::Diff(_) => {
                    let qp_diff = QPDiff { set: None };
                    let qp_idx = qp_dag.add_node(QPNode::Diff(qp_diff));
                    idx_map.insert(idx, qp_idx);
                    for child_idx in query_dag.neighbors_directed(idx, Outgoing) {
                        if let Some(target_idx) = idx_map.get(&child_idx) {
                            let edge_idx = query_dag
                                .find_edge(idx, child_idx)
                                .context("Cannot find edge")?;
                            let weight = query_dag
                                .edge_weight(edge_idx)
                                .context("Cannot find edge")?;
                            qp_dag.add_edge(qp_idx, *target_idx, *weight);
                        } else {
                            bail!("Cannot find the child idx of difference in idx_map");
                        }
                    }
                }
            }
        }
    }

    for q_idx in &q_outputs {
        qp_outputs.insert(*idx_map.get(q_idx).context("index map not matched")?);
    }

    let qp = QueryPlan {
        end_blk_height: query_end_blk_height,
        outputs: qp_outputs,
        dag: qp_dag,
        trie_proofs: query.trie_proofs,
    };

    Ok(qp)
}

pub(crate) fn estimate_query_cost<K: Num, T: ReadInterface<K = K>>(
    inputs: &[NodeIndex],
    dag: &mut Graph<QueryNode<K>, bool>,
    trie_ctx: &mut trie_tree::read::ReadContext<T>,
    chain: &T,
    pk: &AccPublicKey,
) -> Result<usize> {
    let mut cost: usize = 0;
    let mut map = HashMap::<NodeIndex, QueryNode<K>>::new();

    for idx in inputs {
        let mut child_idxs = Vec::<NodeIndex>::new();
        for index in dag.neighbors_directed(*idx, Outgoing) {
            child_idxs.push(index);
        }
        if let Some(node) = dag.node_weight_mut(*idx) {
            match node {
                QueryNode::Range(n) => {
                    if n.set.is_none() {
                        n.estimate_size(chain, pk)?;
                    }
                    map.insert(*idx, node.clone());
                }
                QueryNode::Keyword(n) => {
                    if n.set.is_none() {
                        n.estimate_size(trie_ctx, pk)?;
                    }
                    map.insert(*idx, node.clone());
                }
                QueryNode::BlkRt(n) => {
                    if n.set.is_none() {
                        n.estimate_size(chain, pk)?;
                    }
                    map.insert(*idx, node.clone());
                }
                QueryNode::Union(n) => {
                    if n.set.is_none() {
                        let q_c_idx1 = child_idxs
                            .get(1)
                            .context("Cannot find the first child idx of union")?;
                        let q_c1 = map
                            .get(q_c_idx1)
                            .context("Cannot find the first child node in map")?;
                        let s1 = q_c1.get_set()?;
                        let q_c_idx2 = child_idxs
                            .get(0)
                            .context("Cannot find the first child idx of union")?;
                        let q_c2 = map
                            .get(q_c_idx2)
                            .context("Cannot find the second child node in map")?;
                        let s2 = q_c2.get_set()?;
                        let res_set = (s1) | (s2);
                        let inter_cost = COST_COEFFICIENT * s1.len() * s2.len();
                        cost += inter_cost;
                        n.set = Some(res_set);
                    }
                    map.insert(*idx, node.clone());
                }
                QueryNode::Intersec(n) => {
                    if n.set.is_none() {
                        let q_c_idx1 = child_idxs
                            .get(1)
                            .context("Cannot find the first child idx of intersection")?;
                        let q_c1 = map
                            .get(q_c_idx1)
                            .context("Cannot find the first child node in map")?;
                        let s1 = q_c1.get_set()?;
                        let q_c_idx2 = child_idxs
                            .get(0)
                            .context("Cannot find the first child idx of intersection")?;
                        let q_c2 = map
                            .get(q_c_idx2)
                            .context("Cannot find the second child node in map")?;
                        let s2 = q_c2.get_set()?;
                        let res_set = (s1) & (s2);
                        let inter_cost = COST_COEFFICIENT * s1.len() * s2.len();
                        cost += inter_cost;
                        n.set = Some(res_set);
                    }
                    map.insert(*idx, node.clone());
                }
                QueryNode::Diff(n) => {
                    if n.set.is_none() {
                        let q_c_idx1 = child_idxs
                            .get(0)
                            .context("Cannot find the first child idx of difference")?;
                        let q_c1 = map
                            .get(q_c_idx1)
                            .context("Cannot find the first child node in map")?;
                        let s1 = q_c1.get_set()?;
                        let q_c_idx2 = child_idxs
                            .get(1)
                            .context("Cannot find the first child idx of difference")?;
                        let q_c2 = map
                            .get(q_c_idx2)
                            .context("Cannot find the second child node in map")?;
                        let s2 = q_c2.get_set()?;
                        let res_set = (s1) / (s2);
                        let inter_cost = COST_COEFFICIENT * s1.len() * s2.len();
                        cost += inter_cost;
                        n.set = Some(res_set);
                    }
                    map.insert(*idx, node.clone());
                }
            }
        }
    }

    Ok(cost)
}
