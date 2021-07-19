use crate::{
    acc::{AccPublicKey, AccValue, Set},
    chain::{
        block::Height,
        bplus_tree,
        range::Range,
        traits::{Num, ReadInterface},
        trie_tree, COST_COEFFICIENT,
    },
};
use anyhow::{bail, Context, Result};
use petgraph::{algo::toposort, graph::NodeIndex, EdgeDirection::Outgoing, Graph};
use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet, VecDeque},
    iter::FromIterator,
    num::NonZeroU64,
};

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
    pub fn get_set(&self) -> Result<Set> {
        match self {
            QPNode::Range(n) => Ok(n.set.clone().context("No set in the QPNode")?.0),
            QPNode::Keyword(n) => Ok(n.set.clone().context("No set in the QPNode")?.0),
            QPNode::BlkRt(n) => Ok(n.set.clone().context("No set in the QPNode")?.0),
            QPNode::Union(n) => Ok(n.set.clone().context("No set in the QPNode")?.0),
            QPNode::Intersec(n) => Ok(n.set.clone().context("No set in the QPNode")?.0),
            QPNode::Diff(n) => Ok(n.set.clone().context("No set in the QPNode")?.0),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QPRangeNode<K: Num> {
    pub(crate) range: Range<K>,
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
    pub(crate) dim: usize,
    pub(crate) set: Option<(Set, AccValue, bplus_tree::proof::Proof<K>)>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QPKeywordNode {
    pub(crate) keyword: String,
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
    pub(crate) set: Option<(Set, AccValue)>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QPBlkRtNode {
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
    pub(crate) set: Option<(Set, AccValue)>,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct QPUnion {
    pub(crate) set: Option<(Set, usize, usize)>,
    pub(crate) cost: Option<(usize, usize)>,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct QPIntersec {
    pub(crate) set: Option<(Set, usize, usize)>,
    pub(crate) cost: Option<(usize, usize)>,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct QPDiff {
    pub(crate) set: Option<(Set, usize, usize)>,
    pub(crate) cost: Option<(usize, usize)>,
}

pub struct QueryPlan<K: Num> {
    pub(crate) end_blk_height: Height,
    pub(crate) outputs: HashSet<NodeIndex>,
    pub(crate) dag: Graph<QPNode<K>, ()>,
    pub(crate) trie_proofs: HashMap<Height, trie_tree::proof::Proof>,
}

impl<K: Num> QueryPlan<K> {
    pub fn remove_top_union(&mut self) -> Result<()> {
        let mut queue = VecDeque::<NodeIndex>::new();
        for idx in &self.outputs {
            queue.push_back(*idx);
        }

        while let Some(idx) = queue.pop_front() {
            if let Some(QPNode::Union(_)) = self.dag.node_weight(idx) {
                let cur_max_idx = self.dag.node_indices().last().context("No idx in output")?;
                let child_idxs = self.dag.neighbors_directed(idx, Outgoing);
                self.outputs.remove(&idx);
                for child_idx in child_idxs {
                    if child_idx == cur_max_idx {
                        self.outputs.insert(idx);
                    } else {
                        self.outputs.insert(child_idx);
                    }
                    queue.push_back(child_idx);
                }
                self.dag.remove_node(idx);
            }
        }
        Ok(())
    }

    pub fn estimate_cost<T: ReadInterface<K = K>>(
        &mut self,
        chain: &T,
        pk: &AccPublicKey,
    ) -> Result<usize> {
        let mut qp_inputs = match toposort(&self.dag, None) {
            Ok(v) => v,
            Err(_) => {
                bail!("Input query plan graph not valid")
            }
        };
        qp_inputs.reverse();
        let mut cost: usize = 0;
        let mut map = HashMap::<NodeIndex, QPNode<K>>::new();
        let dag = &mut self.dag;
        let mut trie_ctxes = HashMap::<Height, trie_tree::read::ReadContext<T>>::new();

        for idx in qp_inputs {
            let mut child_idxs = Vec::<NodeIndex>::new();
            for index in dag.neighbors_directed(idx, Outgoing) {
                child_idxs.push(index);
            }
            if let Some(node) = dag.node_weight_mut(idx) {
                match node {
                    QPNode::Range(n) => {
                        if n.set.is_none() {
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
                            n.set = Some((s, a, p));
                        }
                        map.insert(idx, node.clone());
                    }
                    QPNode::Keyword(n) => {
                        if n.set.is_none() {
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
                            n.set = Some((set, acc));
                        }
                        map.insert(idx, node.clone());
                    }
                    QPNode::BlkRt(n) => {
                        if n.set.is_none() {
                            let mut a = AccValue::from_set(&Set::new(), pk);
                            let mut total_obj_id_nums = Vec::<NonZeroU64>::new();
                            for i in 0..n.time_win {
                                if n.blk_height.0 > i {
                                    let blk_content =
                                        chain.read_block_content(Height(n.blk_height.0 - i))?;
                                    let mut obj_id_nums = blk_content.read_obj_id_nums();
                                    total_obj_id_nums.append(&mut obj_id_nums);
                                    let sub_acc = blk_content
                                        .read_acc()
                                        .context("The block does not have acc value")?;
                                    a = a + sub_acc;
                                }
                            }
                            let s = Set::from_iter(total_obj_id_nums.into_iter());
                            n.set = Some((s, a));
                        }
                        map.insert(idx, node.clone());
                    }
                    QPNode::Union(n) => {
                        let qp_c_idx1 = child_idxs
                            .get(1)
                            .context("Cannot find the first child idx of union")?;
                        let qp_c1 = map
                            .get(qp_c_idx1)
                            .context("Cannot find the first child node in map")?;
                        let s1 = qp_c1.get_set()?;
                        let qp_c_idx2 = child_idxs
                            .get(0)
                            .context("Cannot find the first child idx of union")?;
                        let qp_c2 = map
                            .get(qp_c_idx2)
                            .context("Cannot find the second child node in map")?;
                        let s2 = qp_c2.get_set()?;
                        let res_set = (&s1) | (&s2);
                        let inter_cost = COST_COEFFICIENT * s1.len() * s2.len();
                        let mut final_cost = s1.len() * s2.len();
                        if self.outputs.contains(&idx) {
                            final_cost = 0;
                            cost += final_cost;
                        } else {
                            cost += inter_cost;
                        }
                        n.set = Some((res_set, inter_cost, final_cost));
                        map.insert(idx, node.clone());
                    }
                    QPNode::Intersec(n) => {
                        let qp_c_idx1 = child_idxs
                            .get(1)
                            .context("Cannot find the first child idx of intersection")?;
                        let qp_c1 = map
                            .get(qp_c_idx1)
                            .context("Cannot find the first child node in map")?;
                        let s1 = qp_c1.get_set()?;
                        let qp_c_idx2 = child_idxs
                            .get(0)
                            .context("Cannot find the first child idx of intersection")?;
                        let qp_c2 = map
                            .get(qp_c_idx2)
                            .context("Cannot find the second child node in map")?;
                        let s2 = qp_c2.get_set()?;
                        let res_set = (&s1) & (&s2);
                        let inter_cost = COST_COEFFICIENT * s1.len() * s2.len();
                        let final_cost = s1.len() * s2.len();
                        if self.outputs.contains(&idx) {
                            cost += final_cost
                        } else {
                            cost += inter_cost;
                        }
                        n.set = Some((res_set, inter_cost, final_cost));
                        map.insert(idx, node.clone());
                    }
                    QPNode::Diff(n) => {
                        let qp_c_idx1 = child_idxs
                            .get(1)
                            .context("Cannot find the first child idx of difference")?;
                        let qp_c1 = map
                            .get(qp_c_idx1)
                            .context("Cannot find the first child node in map")?;
                        let s1 = qp_c1.get_set()?;
                        let qp_c_idx2 = child_idxs
                            .get(0)
                            .context("Cannot find the first child idx of difference")?;
                        let qp_c2 = map
                            .get(qp_c_idx2)
                            .context("Cannot find the second child node in map")?;
                        let s2 = qp_c2.get_set()?;
                        let res_set = (&s1) / (&s2);
                        let inter_cost = COST_COEFFICIENT * s1.len() * s2.len();
                        let final_cost = s1.len() * s2.len();
                        if self.outputs.contains(&idx) {
                            cost += final_cost
                        } else {
                            cost += inter_cost;
                        }
                        n.set = Some((res_set, inter_cost, final_cost));
                        map.insert(idx, node.clone());
                    }
                }
            }
        }

        Ok(cost)
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{HashMap, HashSet},
        iter::FromIterator,
    };

    use super::{QPKeywordNode, QPNode, QPUnion};
    use crate::chain::{
        block::Height,
        query::query_plan::{QPIntersec, QueryPlan},
        trie_tree,
    };
    use petgraph::{
        dot::{Config, Dot},
        graph::NodeIndex,
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
        let union = QPUnion {
            set: None,
            cost: None,
        };
        let intersec = QPIntersec {
            set: None,
            cost: None,
        };

        let mut qp_dag = Graph::<QPNode<u32>, ()>::new();
        let idx0 = qp_dag.add_node(QPNode::Keyword(Box::new(k1.clone())));
        let idx1 = qp_dag.add_node(QPNode::Keyword(Box::new(k2.clone())));
        let idx2 = qp_dag.add_node(QPNode::Intersec(intersec.clone()));
        qp_dag.add_edge(idx2, idx0, ());
        qp_dag.add_edge(idx2, idx1, ());
        let mut qp = QueryPlan {
            end_blk_height: Height(0),
            outputs: HashSet::<NodeIndex>::from_iter(vec![idx2].into_iter()),
            dag: qp_dag,
            trie_proofs: HashMap::<Height, trie_tree::proof::Proof>::new(),
        };
        println!("before removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        qp.remove_top_union().unwrap();
        println!("after removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        println!("=======================");
        assert_eq!(
            qp.outputs,
            HashSet::<NodeIndex>::from_iter(vec![idx2].into_iter())
        );

        let mut qp_dag = Graph::<QPNode<u32>, ()>::new();
        let idx0 = qp_dag.add_node(QPNode::Keyword(Box::new(k1.clone())));
        let idx1 = qp_dag.add_node(QPNode::Keyword(Box::new(k2.clone())));
        let idx2 = qp_dag.add_node(QPNode::Union(union.clone()));
        qp_dag.add_edge(idx2, idx0, ());
        qp_dag.add_edge(idx2, idx1, ());
        let mut qp = QueryPlan {
            end_blk_height: Height(0),
            outputs: HashSet::<NodeIndex>::from_iter(vec![idx2].into_iter()),
            dag: qp_dag,
            trie_proofs: HashMap::<Height, trie_tree::proof::Proof>::new(),
        };
        println!("before removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        qp.remove_top_union().unwrap();
        println!("after removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        println!("=======================");
        assert_eq!(
            qp.outputs,
            HashSet::<NodeIndex>::from_iter(vec![idx0, idx1].into_iter())
        );

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
            outputs: HashSet::<NodeIndex>::from_iter(vec![idx4].into_iter()),
            dag: qp_dag,
            trie_proofs: HashMap::<Height, trie_tree::proof::Proof>::new(),
        };
        println!("before removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        qp.remove_top_union().unwrap();
        println!("after removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        println!("=======================");
        assert_eq!(
            qp.outputs,
            HashSet::<NodeIndex>::from_iter(vec![idx2, idx3].into_iter())
        );

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
            outputs: HashSet::<NodeIndex>::from_iter(vec![idx4].into_iter()),
            dag: qp_dag,
            trie_proofs: HashMap::<Height, trie_tree::proof::Proof>::new(),
        };
        println!("before removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        qp.remove_top_union().unwrap();
        println!("after removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        println!("=======================");
        assert_eq!(
            qp.outputs,
            HashSet::<NodeIndex>::from_iter(vec![idx2, idx1, idx0].into_iter())
        );

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
            outputs: HashSet::<NodeIndex>::from_iter(vec![idx6].into_iter()),
            dag: qp_dag,
            trie_proofs: HashMap::<Height, trie_tree::proof::Proof>::new(),
        };
        println!("before removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        qp.remove_top_union().unwrap();
        println!("after removing top unions:");
        println!("{:?}", Dot::with_config(&qp.dag, &[Config::EdgeNoLabel]));
        println!("=======================");
        assert_eq!(
            qp.outputs,
            HashSet::<NodeIndex>::from_iter(vec![idx3, idx2, idx1, idx0].into_iter())
        );
    }
}
