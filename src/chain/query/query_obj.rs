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

#[derive(Debug, Serialize, Deserialize)]
pub enum QueryNode<K: Num> {
    Range(RangeNode<K>),
    Keyword(Box<KeywordNode>),
    BlkRt(Box<BlkRtNode>),
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
    pub(crate) set: Option<(Set, AccValue, bplus_tree::proof::Proof<K>)>,
}

impl<K: Num> RangeNode<K> {
    pub fn estimate_size<T: ReadInterface<K = K>>(
        &mut self,
        chain: &T,
        pk: &AccPublicKey,
    ) -> Result<(usize, Set)> {
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
            let size = s.len();
            self.set = Some((s.clone(), a, p));
            Ok((size, s))
        } else {
            let set_ref = self.set.as_ref().context("No set found")?;
            Ok((set_ref.0.len(), set_ref.0.clone()))
        }
    }
}

#[derive(Default, Debug, Serialize, Deserialize)]
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
    ) -> Result<(usize, Set)> {
        if self.set.is_none() {
            let keyword = self.keyword.clone();
            let (s, a) = trie_ctx.query(keyword, pk)?;
            let size = s.len();
            self.set = Some((s.clone(), a));
            Ok((size, s))
        } else {
            let set_ref = self.set.as_ref().context("No set found")?;
            Ok((set_ref.0.len(), set_ref.0.clone()))
        }
    }
}

#[derive(Default, Debug, Serialize, Deserialize)]
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
    ) -> Result<(usize, Set)> {
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
            let size = s.len();
            self.set = Some((s.clone(), a));
            Ok((size, s))
        } else {
            let set_ref = self.set.as_ref().context("No set found")?;
            Ok((set_ref.0.len(), set_ref.0.clone()))
        }
    }
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
    pub(crate) trie_proofs: HashMap<Height, trie_tree::proof::Proof>,
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
                    let qp_union = QPUnion {
                        set: None,
                        cost: None,
                    };
                    let qp_idx = qp_dag.add_node(QPNode::Union(qp_union));
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
                    let qp_intersec = QPIntersec {
                        set: None,
                        cost: None,
                    };
                    let qp_idx = qp_dag.add_node(QPNode::Intersec(qp_intersec));
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
                    let qp_diff = QPDiff {
                        set: None,
                        cost: None,
                    };
                    let qp_idx = qp_dag.add_node(QPNode::Diff(qp_diff));
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
