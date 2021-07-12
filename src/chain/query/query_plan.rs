use crate::{
    acc::{set::Set, AccValue},
    chain::{block::Height, bplus_tree, range::Range, traits::Num, trie_tree},
};
use anyhow::{Context, Result};
use petgraph::{graph::NodeIndex, EdgeDirection::Outgoing, Graph};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, VecDeque};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum QPNode<K: Num> {
    Range(QPRangeNode<K>),
    Keyword(Box<QPKeywordNode>),
    BlkRt(Box<QPBlkRtNode>),
    Union(QPUnion),
    Intersec(QPIntersec),
    Diff(QPDiff),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QPRangeNode<K: Num> {
    pub(crate) range: Range<K>,
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
    pub(crate) dim: usize,
    pub(crate) set: Option<(Set, AccValue, u32, u32)>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QPKeywordNode {
    pub(crate) keyword: String,
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
    pub(crate) set: Option<(Set, AccValue, u32, u32)>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QPBlkRtNode {
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
    pub(crate) set: Option<(Set, u32, u32)>,
    pub(crate) acc: Option<AccValue>,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct QPUnion {
    pub(crate) set: Option<(Set, u32, u32)>,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct QPIntersec {
    pub(crate) set: Option<(Set, u32, u32)>,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct QPDiff {
    pub(crate) set: Option<(Set, u32, u32)>,
}

pub struct QueryPlan<K: Num> {
    pub(crate) end_blk_height: Height,
    pub(crate) inputs: Vec<NodeIndex>,
    pub(crate) outputs: Vec<NodeIndex>,
    pub(crate) dag: Graph<QPNode<K>, ()>,
    pub(crate) trie_proofs: HashMap<Height, trie_tree::proof::Proof>,
    pub(crate) bplus_proofs: HashMap<Height, HashMap<usize, bplus_tree::proof::Proof<K>>>,
}

impl<K: Num> QueryPlan<K> {
    pub fn remove_top_union(&mut self) -> Result<()> {
        let mut queue = VecDeque::from(self.outputs.clone());

        let qp_dag = self.dag.clone();
        while let Some(idx) = queue.pop_front() {
            if let Some(QPNode::Union(_)) = self.dag.node_weight(idx) {
                let cur_max_idx = self.dag.node_indices().last().context("No idx in output")?;
                let child_idxs = qp_dag.neighbors_directed(idx, Outgoing);
                self.dag.remove_node(idx);
                self.inputs.retain(|&x| x != cur_max_idx);
                self.outputs.retain(|&x| x != idx);
                for child_idx in child_idxs {
                    if child_idx == cur_max_idx {
                        self.outputs.push(idx);
                    } else {
                        self.outputs.push(child_idx);
                    }
                    queue.push_back(child_idx);
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{QPKeywordNode, QPNode, QPUnion};
    use crate::chain::{
        block::Height,
        bplus_tree,
        query::query_plan::{QPIntersec, QueryPlan},
        trie_tree,
    };
    use petgraph::{Graph, dot::{Config, Dot}};
    use std::collections::HashMap;

    #[test]
    fn test_graph_remove() {
        let mut graph = Graph::<u32, ()>::new();
        let id0 = graph.add_node(0);
        let id1 = graph.add_node(1);
        let id2 = graph.add_node(2);
        let id3 = graph.add_node(3);
        let id4 = graph.add_node(4);

        graph.extend_with_edges(&[(id0, id1), (id0, id4), (id1, id2), (id1, id3)]);
        let idx_itr = graph.node_indices();
        println!("{:?}", idx_itr.last());
        println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
        println!("after removing the root node");
        graph.remove_node(id0);
        let idx_itr = graph.node_indices();
        println!("{:?}", idx_itr.last());
        println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
        graph.remove_node(id1);
        let idx_itr = graph.node_indices();
        println!("{:?}", idx_itr.last());
        println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
        assert_eq!(1, 1);
    }

    #[test]
    fn test_remove_union() {
        let k1 = QPKeywordNode {
            keyword: "a".to_string(),
            blk_height: Height(0),
            time_win: 2,
            set: None,
        };
        let k2 = QPKeywordNode {
            keyword: "b".to_string(),
            blk_height: Height(0),
            time_win: 2,
            set: None,
        };
        let k3 = QPKeywordNode {
            keyword: "c".to_string(),
            blk_height: Height(0),
            time_win: 2,
            set: None,
        };
        let k4 = QPKeywordNode {
            keyword: "d".to_string(),
            blk_height: Height(0),
            time_win: 2,
            set: None,
        };
        let union = QPUnion { set: None };
        let intersec = QPIntersec { set: None };

        let mut qp_dag = Graph::<QPNode<u32>, ()>::new();
        let idx0 = qp_dag.add_node(QPNode::Keyword(Box::new(k1.clone())));
        let idx1 = qp_dag.add_node(QPNode::Keyword(Box::new(k2.clone())));
        let idx2 = qp_dag.add_node(QPNode::Intersec(intersec.clone()));
        qp_dag.add_edge(idx2, idx0, ());
        qp_dag.add_edge(idx2, idx1, ());
        let mut qp = QueryPlan {
            end_blk_height: Height(0),
            inputs: vec![idx0, idx1, idx2],
            outputs: vec![idx2],
            dag: qp_dag,
            trie_proofs: HashMap::<Height, trie_tree::proof::Proof>::new(),
            bplus_proofs: HashMap::<Height, HashMap<usize, bplus_tree::proof::Proof<u32>>>::new(),
        };
        println!("before removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        qp.remove_top_union().unwrap();
        println!("after removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        println!("=======================");
        assert_eq!(qp.inputs, vec![idx0, idx1, idx2]);
        assert_eq!(qp.outputs, vec![idx2]);

        let mut qp_dag = Graph::<QPNode<u32>, ()>::new();
        let idx0 = qp_dag.add_node(QPNode::Keyword(Box::new(k1.clone())));
        let idx1 = qp_dag.add_node(QPNode::Keyword(Box::new(k2.clone())));
        let idx2 = qp_dag.add_node(QPNode::Union(union.clone()));
        qp_dag.add_edge(idx2, idx0, ());
        qp_dag.add_edge(idx2, idx1, ());
        let mut qp = QueryPlan {
            end_blk_height: Height(0),
            inputs: vec![idx0, idx1, idx2],
            outputs: vec![idx2],
            dag: qp_dag,
            trie_proofs: HashMap::<Height, trie_tree::proof::Proof>::new(),
            bplus_proofs: HashMap::<Height, HashMap<usize, bplus_tree::proof::Proof<u32>>>::new(),
        };
        println!("before removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        qp.remove_top_union().unwrap();
        println!("after removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        println!("=======================");
        assert_eq!(qp.inputs, vec![idx0, idx1]);
        assert_eq!(qp.outputs, vec![idx1, idx0]);

        let mut qp_dag = Graph::<QPNode<u32>, ()>::new();
        let idx0 = qp_dag.add_node(QPNode::Keyword(Box::new(k1.clone())));
        let idx1 = qp_dag.add_node(QPNode::Keyword(Box::new(k2.clone())));
        let idx2 = qp_dag.add_node(QPNode::Keyword(Box::new(k3.clone())));
        let idx3 = qp_dag.add_node(QPNode::Intersec(intersec.clone()));
        let idx4 = qp_dag.add_node(QPNode::Union(union.clone()));

        qp_dag.add_edge(idx3, idx0, ());
        qp_dag.add_edge(idx3, idx1, ());
        qp_dag.add_edge(idx4, idx3, ());
        qp_dag.add_edge(idx4, idx2, ());
        let mut qp = QueryPlan {
            end_blk_height: Height(0),
            inputs: vec![idx0, idx1, idx2, idx3, idx4],
            outputs: vec![idx4],
            dag: qp_dag,
            trie_proofs: HashMap::<Height, trie_tree::proof::Proof>::new(),
            bplus_proofs: HashMap::<Height, HashMap<usize, bplus_tree::proof::Proof<u32>>>::new(),
        };
        println!("before removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        qp.remove_top_union().unwrap();
        println!("after removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        println!("=======================");
        assert_eq!(qp.inputs, vec![idx0, idx1, idx2, idx3]);
        assert_eq!(qp.outputs, vec![idx2, idx3]);

        let mut qp_dag = Graph::<QPNode<u32>, ()>::new();
        let idx0 = qp_dag.add_node(QPNode::Keyword(Box::new(k1.clone())));
        let idx1 = qp_dag.add_node(QPNode::Keyword(Box::new(k2.clone())));
        let idx2 = qp_dag.add_node(QPNode::Keyword(Box::new(k3.clone())));
        let idx3 = qp_dag.add_node(QPNode::Union(union.clone()));
        let idx4 = qp_dag.add_node(QPNode::Union(union.clone()));

        qp_dag.add_edge(idx3, idx0, ());
        qp_dag.add_edge(idx3, idx1, ());
        qp_dag.add_edge(idx4, idx3, ());
        qp_dag.add_edge(idx4, idx2, ());
        let mut qp = QueryPlan {
            end_blk_height: Height(0),
            inputs: vec![idx0, idx1, idx2, idx3, idx4],
            outputs: vec![idx4],
            dag: qp_dag,
            trie_proofs: HashMap::<Height, trie_tree::proof::Proof>::new(),
            bplus_proofs: HashMap::<Height, HashMap<usize, bplus_tree::proof::Proof<u32>>>::new(),
        };
        println!("before removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        qp.remove_top_union().unwrap();
        println!("after removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        println!("=======================");
        assert_eq!(qp.inputs, vec![idx0, idx1, idx2]);
        assert_eq!(qp.outputs, vec![idx2, idx1, idx0]);

        let mut qp_dag = Graph::<QPNode<u32>, ()>::new();
        let idx0 = qp_dag.add_node(QPNode::Keyword(Box::new(k1.clone())));
        let idx1 = qp_dag.add_node(QPNode::Keyword(Box::new(k2.clone())));
        let idx2 = qp_dag.add_node(QPNode::Keyword(Box::new(k3.clone())));
        let idx3 = qp_dag.add_node(QPNode::Keyword(Box::new(k4.clone())));
        let idx4 = qp_dag.add_node(QPNode::Union(union.clone()));
        let idx5 = qp_dag.add_node(QPNode::Union(union.clone()));
        let idx6 = qp_dag.add_node(QPNode::Union(union.clone()));

        qp_dag.add_edge(idx4, idx0, ());
        qp_dag.add_edge(idx4, idx1, ());
        qp_dag.add_edge(idx5, idx2, ());
        qp_dag.add_edge(idx5, idx3, ());
        qp_dag.add_edge(idx6, idx4, ());
        qp_dag.add_edge(idx6, idx5, ());
        let mut qp = QueryPlan {
            end_blk_height: Height(0),
            inputs: vec![idx0, idx1, idx2, idx3, idx4, idx5, idx6],
            outputs: vec![idx6],
            dag: qp_dag,
            trie_proofs: HashMap::<Height, trie_tree::proof::Proof>::new(),
            bplus_proofs: HashMap::<Height, HashMap<usize, bplus_tree::proof::Proof<u32>>>::new(),
        };
        println!("before removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        qp.remove_top_union().unwrap();
        println!("after removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        println!("=======================");
        assert_eq!(qp.inputs, vec![idx0, idx1, idx2, idx3]);
        assert_eq!(qp.outputs, vec![idx3, idx2, idx1, idx0]);
    }
}
