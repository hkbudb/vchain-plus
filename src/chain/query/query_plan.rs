use crate::{
    acc::{AccValue, Set},
    chain::{block::Height, bplus_tree, traits::Num, trie_tree},
};
use anyhow::{Context, Result};
use petgraph::{graph::NodeIndex, EdgeDirection::Outgoing, Graph};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet, VecDeque};

use super::query_dag::DagNode;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum QPNode<K: Num> {
    Range(QPRangeNode<K>),
    Keyword(Box<QPKeywordNode>),
    BlkRt(Box<QPBlkRtNode>),
    Union(QPUnion),
    Intersec(QPIntersec),
    Diff(QPDiff),
}

impl<K: Num> QPNode<K> {
    pub fn get_set(&self) -> Result<&Set> {
        match self {
            QPNode::Range(n) => Ok(&n.set.as_ref().context("No set in the QPNode")?.0),
            QPNode::Keyword(n) => Ok(&n.set.as_ref().context("No set in the QPNode")?.0),
            QPNode::BlkRt(n) => Ok(&n.set.as_ref().context("No set in the QPNode")?.0),
            QPNode::Union(n) => Ok(&n.set.as_ref().context("No set in the QPNode")?.0),
            QPNode::Intersec(n) => Ok(&n.set.as_ref().context("No set in the QPNode")?.0),
            QPNode::Diff(n) => Ok(&n.set.as_ref().context("No set in the QPNode")?.0),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QPRangeNode<K: Num> {
    pub(crate) blk_height: Height,
    pub(crate) set: Option<(Set, AccValue, bplus_tree::proof::Proof<K>)>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QPKeywordNode {
    pub(crate) blk_height: Height,
    pub(crate) set: Option<(Set, AccValue)>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QPBlkRtNode {
    pub(crate) blk_height: Height,
    pub(crate) set: Option<(Set, AccValue)>,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct QPUnion {
    pub(crate) set: Option<(Set, usize, usize)>,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct QPIntersec {
    pub(crate) set: Option<(Set, usize, usize)>,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct QPDiff {
    pub(crate) set: Option<(Set, usize, usize)>,
}

#[derive(Debug)]
pub struct QueryPlan<K: Num> {
    pub(crate) end_blk_height: Height,
    pub(crate) outputs: HashSet<NodeIndex>,
    pub(crate) dag_content: HashMap<NodeIndex, QPNode<K>>,
    pub(crate) trie_proofs: HashMap<Height, trie_tree::proof::Proof>,
}

impl<K: Num> QueryPlan<K> {
    pub fn remove_top_union(&mut self, dag: &mut Graph<DagNode<K>, bool>) -> Result<()> {
        let mut queue = VecDeque::<NodeIndex>::new();
        for idx in &self.outputs {
            queue.push_back(*idx);
        }
        while let Some(idx) = queue.pop_front() {
            if let Some(QPNode::Union(_)) = self.dag_content.get(&idx) {
                let cur_max_idx = dag.node_indices().last().context("No idx in output")?;
                let child_idxs = dag.neighbors_directed(idx, Outgoing);
                self.outputs.remove(&idx);
                self.dag_content.remove(&idx);
                for child_idx in child_idxs {
                    if child_idx == cur_max_idx {
                        self.outputs.insert(idx);
                    } else {
                        self.outputs.insert(child_idx);
                    }
                    queue.push_back(child_idx);
                }
                dag.remove_node(idx);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use petgraph::{
        dot::{Config, Dot},
        Graph,
    };

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
}
