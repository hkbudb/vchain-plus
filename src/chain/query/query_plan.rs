use crate::{
    acc::{AccValue, Set},
    chain::{block::Height, bplus_tree, traits::Num, trie_tree},
};
use anyhow::{Context, Result};
use petgraph::graph::NodeIndex;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum QPNode<K: Num> {
    Range(Box<QPRangeNode<K>>),
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
            QPNode::Union(n) => Ok(n.set.as_ref().context("No set in the QPNode")?),
            QPNode::Intersec(n) => Ok(n.set.as_ref().context("No set in the QPNode")?),
            QPNode::Diff(n) => Ok(n.set.as_ref().context("No set in the QPNode")?),
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
    pub(crate) set: Option<Set>,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct QPIntersec {
    pub(crate) set: Option<Set>,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct QPDiff {
    pub(crate) set: Option<Set>,
}

#[derive(Debug)]
pub struct QueryPlan<K: Num> {
    pub(crate) end_blk_height: Height,
    pub(crate) root_idx: NodeIndex,
    pub(crate) dag_content: HashMap<NodeIndex, QPNode<K>>,
    pub(crate) trie_proofs: HashMap<Height, trie_tree::proof::Proof>,
}

impl<K: Num> QueryPlan<K> {
    pub(crate) fn update_root_idx(&mut self, new_idx: NodeIndex) {
        self.root_idx = new_idx;
    }
    pub(crate) fn get_dag_cont(&self) -> &HashMap<NodeIndex, QPNode<K>> {
        &self.dag_content
    }
    pub(crate) fn get_dag_cont_mut(&mut self) -> &mut HashMap<NodeIndex, QPNode<K>> {
        &mut self.dag_content
    }
    pub(crate) fn update_dag_cont(&mut self, dag_cont: HashMap<NodeIndex, QPNode<K>>) {
        self.dag_content = dag_cont;
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
