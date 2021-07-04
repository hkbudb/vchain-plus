use super::query_plan::QueryPlan;
use crate::chain::{
    block::Height,
    bplus_tree,
    query::query_plan::{
        QPBlkRtNode, QPDiff, QPIntersec, QPKeywordNode, QPNode, QPRangeNode, QPUnion,
    },
    range::Range,
    traits::Num,
    trie_tree,
};
use anyhow::{Context, Result, bail};
use petgraph::{algo::toposort, graph::NodeIndex, EdgeDirection::Outgoing, Graph};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Serialize, Deserialize)]
pub enum QueryNode<K: Num> {
    Range(RangeNode<K>),
    Keyword(KeywordNode),
    BlkRt(BlkRtNode),
    Union(UnionNode),
    Intersec(IntersecNode),
    Diff(DiffNode),
}

#[derive(Debug, Serialize, Deserialize)]
pub struct RangeNode<K: Num> {
    pub(crate) range: Range<K>,
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
    pub(crate) dim: usize,
}

#[derive(Default, Debug, Serialize, Deserialize)]
pub struct KeywordNode {
    pub(crate) keyword: String,
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
}

#[derive(Default, Debug, Serialize, Deserialize)]
pub struct BlkRtNode {
    pub(crate) blk_height: Height,
}

#[derive(Default, Debug, Serialize, Deserialize)]
pub struct UnionNode {}

#[derive(Default, Debug, Serialize, Deserialize)]
pub struct IntersecNode {}

#[derive(Default, Debug, Serialize, Deserialize)]
pub struct DiffNode {}

#[derive(Debug)]
pub struct Query<K: Num> {
    pub(crate) end_blk_height: Height,
    pub(crate) query_dag: Graph<QueryNode<K>, ()>,
}

pub fn query_to_qp<K: Num>(query: Query<K>) -> Result<QueryPlan<K>> {
    let mut qp_dag = Graph::<QPNode<K>, ()>::new();
    let query_dag = query.query_dag;
    let query_end_blk_height = query.end_blk_height;
    let mut q_inputs = match toposort(&query_dag, None) {
        Ok(v) => v,
        Err(_) => {
            bail!("Input query graph not valid")
        }
    };
    q_inputs.reverse();
    let qp_output_elm = q_inputs.last().cloned().context("Input query graph is empty")?;
    let mut idx_map = HashMap::<NodeIndex, NodeIndex>::new();
    let mut qp_inputs = Vec::<NodeIndex>::new();
    let qp_outputs = vec![qp_output_elm];

    for idx in q_inputs {
        if let Some(node) = query_dag.node_weight(idx) {
            match node {
                QueryNode::Range(n) => {
                    let qp_range_node = QPRangeNode {
                        range: n.range,
                        blk_height: n.blk_height,
                        time_win: n.time_win,
                        dim: n.dim,
                        set: None,
                    };
                    let qp_idx = qp_dag.add_node(QPNode::Range(qp_range_node));
                    qp_inputs.push(qp_idx);
                    idx_map.insert(idx, qp_idx);
                }
                QueryNode::Keyword(n) => {
                    let qp_keyword_node = QPKeywordNode {
                        keyword: n.keyword.clone(),
                        blk_height: n.blk_height,
                        time_win: n.time_win,
                        set: None,
                    };
                    let qp_idx = qp_dag.add_node(QPNode::Keyword(Box::new(qp_keyword_node)));
                    qp_inputs.push(qp_idx);
                    idx_map.insert(idx, qp_idx);
                }
                QueryNode::BlkRt(n) => {
                    let qp_blk_rt_node = QPBlkRtNode {
                        blk_height: n.blk_height,
                        set: None,
                        acc: None,
                    };
                    let qp_idx = qp_dag.add_node(QPNode::BlkRt(Box::new(qp_blk_rt_node)));
                    qp_inputs.push(qp_idx);
                    idx_map.insert(idx, qp_idx);
                }
                QueryNode::Union(_) => {
                    let qp_union = QPUnion { set: None };
                    let qp_idx = qp_dag.add_node(QPNode::Union(qp_union));
                    qp_inputs.push(qp_idx);
                    idx_map.insert(idx, qp_idx);
                    for child_idx in query_dag.neighbors_directed(idx, Outgoing) {
                        if let Some(target_idx) = idx_map.get(&child_idx) {
                            qp_dag.add_edge(qp_idx, *target_idx, ());
                        } else {
                            bail!("Cannot find the child idx of union in idx_map");
                        }
                    }
                }
                QueryNode::Intersec(_) => {
                    let qp_intersec = QPIntersec { set: None };
                    let qp_idx = qp_dag.add_node(QPNode::Intersec(qp_intersec));
                    qp_inputs.push(qp_idx);
                    idx_map.insert(idx, qp_idx);
                    for child_idx in query_dag.neighbors_directed(idx, Outgoing) {
                        if let Some(target_idx) = idx_map.get(&child_idx) {
                            qp_dag.add_edge(qp_idx, *target_idx, ());
                        } else {
                            bail!("Cannot find the child idx of intersection in idx_map");
                        }
                    }
                }
                QueryNode::Diff(_) => {
                    let qp_diff = QPDiff { set: None };
                    let qp_idx = qp_dag.add_node(QPNode::Diff(qp_diff));
                    qp_inputs.push(qp_idx);
                    idx_map.insert(idx, qp_idx);
                    for child_idx in query_dag.neighbors_directed(idx, Outgoing) {
                        if let Some(target_idx) = idx_map.get(&child_idx) {
                            qp_dag.add_edge(qp_idx, *target_idx, ());
                        } else {
                            bail!("Cannot find the child idx of difference in idx_map");
                        }
                    }
                }
            }
        }
    }

    let qp_trie_proofs = HashMap::<Height, trie_tree::proof::Proof>::new();
    let qp_bplus_proofs = HashMap::<Height, HashMap<usize, bplus_tree::proof::Proof<K>>>::new();
    let qp = QueryPlan {
        end_blk_height: query_end_blk_height,
        inputs: qp_inputs,
        outputs: qp_outputs,
        dag: qp_dag,
        trie_proofs: qp_trie_proofs,
        bplus_proofs: qp_bplus_proofs,
    };

    Ok(qp)
}
