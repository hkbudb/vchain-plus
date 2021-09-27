use crate::{
    acc::{AccPublicKey, Set},
    chain::{
        block::Height,
        bplus_tree,
        query::{
            query_param::{AndNode, Node, NotNode, OrNode},
            query_plan::{
                QPBlkRtNode, QPDiff, QPIntersec, QPKeywordNode, QPNode, QPRangeNode, QPUnion,
            },
            QueryContent,
        },
        range::Range,
        traits::{Num, ReadInterface},
        trie_tree, COST_COEFFICIENT,
    },
};
use anyhow::{bail, Context, Result};
use petgraph::{
    algo::toposort,
    graph::NodeIndex,
    EdgeDirection::{Incoming, Outgoing},
    Graph,
};
use serde::{Deserialize, Serialize};
use smol_str::SmolStr;
use std::collections::{HashMap, VecDeque};

use super::{query_plan::QueryPlan, TimeWin};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum DagNode<K: Num> {
    Range(RangeNode<K>),
    Keyword(Box<KeywordNode>),
    BlkRt(Box<BlkRtNode>),
    Union(UnionNode),
    Intersec(IntersecNode),
    Diff(DiffNode),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RangeNode<K: Num> {
    pub(crate) range: Range<K>,
    pub(crate) dim: usize,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct KeywordNode {
    pub(crate) keyword: String,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct BlkRtNode {}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct UnionNode {}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct IntersecNode {}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct DiffNode {}

// return the root idx of added keyword expression
fn query_dag_add_keyword_exp<K: Num>(
    keyword_exp: &Node,
    dag: &mut Graph<DagNode<K>, bool>,
) -> Result<NodeIndex> {
    let mut queue = VecDeque::<(&Node, NodeIndex)>::new();
    let mut idx_map = HashMap::<String, NodeIndex>::new();
    let keyword_root_idx: NodeIndex;
    match keyword_exp {
        Node::And(n) => {
            let idx = dag.add_node(DagNode::Intersec(IntersecNode {}));
            keyword_root_idx = idx;
            let AndNode(c1, c2) = n.as_ref();
            let idx1: NodeIndex;
            let idx2: NodeIndex;
            match c1 {
                Node::And(_) => {
                    idx1 = dag.add_node(DagNode::Intersec(IntersecNode {}));
                }
                Node::Or(_) => {
                    idx1 = dag.add_node(DagNode::Union(UnionNode {}));
                }
                Node::Not(_) => {
                    idx1 = dag.add_node(DagNode::Diff(DiffNode {}));
                }
                Node::Input(s) => {
                    idx1 = dag.add_node(DagNode::Keyword(Box::new(KeywordNode {
                        keyword: s.to_string(),
                    })));
                    idx_map.insert(s.to_string(), idx1);
                }
            }
            dag.add_edge(idx, idx1, true);
            match c2 {
                Node::And(_) => {
                    idx2 = dag.add_node(DagNode::Intersec(IntersecNode {}));
                }
                Node::Or(_) => {
                    idx2 = dag.add_node(DagNode::Union(UnionNode {}));
                }
                Node::Not(_) => {
                    idx2 = dag.add_node(DagNode::Diff(DiffNode {}));
                }
                Node::Input(s) => {
                    idx2 = dag.add_node(DagNode::Keyword(Box::new(KeywordNode {
                        keyword: s.to_string(),
                    })));
                    idx_map.insert(s.to_string(), idx2);
                }
            }
            dag.add_edge(idx, idx2, false);
            queue.push_back((c1, idx1));
            queue.push_back((c2, idx2));
        }
        Node::Or(n) => {
            let idx = dag.add_node(DagNode::Union(UnionNode {}));
            keyword_root_idx = idx;
            let OrNode(c1, c2) = n.as_ref();
            let idx1: NodeIndex;
            let idx2: NodeIndex;
            match c1 {
                Node::And(_) => {
                    idx1 = dag.add_node(DagNode::Intersec(IntersecNode {}));
                }
                Node::Or(_) => {
                    idx1 = dag.add_node(DagNode::Union(UnionNode {}));
                }
                Node::Not(_) => {
                    idx1 = dag.add_node(DagNode::Diff(DiffNode {}));
                }
                Node::Input(s) => {
                    idx1 = dag.add_node(DagNode::Keyword(Box::new(KeywordNode {
                        keyword: s.to_string(),
                    })));
                    idx_map.insert(s.to_string(), idx1);
                }
            }
            dag.add_edge(idx, idx1, true);
            match c2 {
                Node::And(_) => {
                    idx2 = dag.add_node(DagNode::Intersec(IntersecNode {}));
                }
                Node::Or(_) => {
                    idx2 = dag.add_node(DagNode::Union(UnionNode {}));
                }
                Node::Not(_) => {
                    idx2 = dag.add_node(DagNode::Diff(DiffNode {}));
                }
                Node::Input(s) => {
                    idx2 = dag.add_node(DagNode::Keyword(Box::new(KeywordNode {
                        keyword: s.to_string(),
                    })));
                    idx_map.insert(s.to_string(), idx2);
                }
            }
            dag.add_edge(idx, idx2, false);
            queue.push_back((c1, idx1));
            queue.push_back((c2, idx2));
        }
        Node::Not(n) => {
            let idx = dag.add_node(DagNode::Diff(DiffNode {}));
            keyword_root_idx = idx;
            let NotNode(c) = n.as_ref();
            let c_idx: NodeIndex;
            match c {
                Node::And(_) => {
                    c_idx = dag.add_node(DagNode::Intersec(IntersecNode {}));
                }
                Node::Or(_) => {
                    c_idx = dag.add_node(DagNode::Union(UnionNode {}));
                }
                Node::Not(_) => {
                    c_idx = dag.add_node(DagNode::Diff(DiffNode {}));
                }
                Node::Input(s) => {
                    c_idx = dag.add_node(DagNode::Keyword(Box::new(KeywordNode {
                        keyword: s.to_string(),
                    })));
                    idx_map.insert(s.to_string(), c_idx);
                }
            }
            dag.add_edge(idx, c_idx, true);
            let blk_rt_idx = dag.add_node(DagNode::BlkRt(Box::new(BlkRtNode {})));
            dag.add_edge(idx, blk_rt_idx, false);
            queue.push_back((c, c_idx));
        }
        Node::Input(s) => {
            let idx = dag.add_node(DagNode::Keyword(Box::new(KeywordNode {
                keyword: s.to_string(),
            })));
            keyword_root_idx = idx;
        }
    }

    while let Some((node, idx)) = queue.pop_front() {
        match node {
            Node::And(n) => {
                let AndNode(c1, c2) = n.as_ref();
                let idx1: NodeIndex;
                let idx2: NodeIndex;
                match c1 {
                    Node::And(_) => {
                        idx1 = dag.add_node(DagNode::Intersec(IntersecNode {}));
                    }
                    Node::Or(_) => {
                        idx1 = dag.add_node(DagNode::Union(UnionNode {}));
                    }
                    Node::Not(_) => {
                        idx1 = dag.add_node(DagNode::Diff(DiffNode {}));
                    }
                    Node::Input(s) => {
                        if let Some(c_idx) = idx_map.get(s) {
                            idx1 = *c_idx;
                        } else {
                            idx1 = dag.add_node(DagNode::Keyword(Box::new(KeywordNode {
                                keyword: s.to_string(),
                            })));
                            idx_map.insert(s.to_string(), idx1);
                        }
                    }
                }
                dag.add_edge(idx, idx1, true);
                match c2 {
                    Node::And(_) => {
                        idx2 = dag.add_node(DagNode::Intersec(IntersecNode {}));
                    }
                    Node::Or(_) => {
                        idx2 = dag.add_node(DagNode::Union(UnionNode {}));
                    }
                    Node::Not(_) => {
                        idx2 = dag.add_node(DagNode::Diff(DiffNode {}));
                    }
                    Node::Input(s) => {
                        if let Some(c_idx) = idx_map.get(s) {
                            idx2 = *c_idx;
                        } else {
                            idx2 = dag.add_node(DagNode::Keyword(Box::new(KeywordNode {
                                keyword: s.to_string(),
                            })));
                            idx_map.insert(s.to_string(), idx2);
                        }
                    }
                }
                dag.add_edge(idx, idx2, false);
                queue.push_back((c1, idx1));
                queue.push_back((c2, idx2));
            }
            Node::Or(n) => {
                let OrNode(c1, c2) = n.as_ref();
                let idx1: NodeIndex;
                let idx2: NodeIndex;
                match c1 {
                    Node::And(_) => {
                        idx1 = dag.add_node(DagNode::Intersec(IntersecNode {}));
                    }
                    Node::Or(_) => {
                        idx1 = dag.add_node(DagNode::Union(UnionNode {}));
                    }
                    Node::Not(_) => {
                        idx1 = dag.add_node(DagNode::Diff(DiffNode {}));
                    }
                    Node::Input(s) => {
                        if let Some(c_idx) = idx_map.get(s) {
                            idx1 = *c_idx;
                        } else {
                            idx1 = dag.add_node(DagNode::Keyword(Box::new(KeywordNode {
                                keyword: s.to_string(),
                            })));
                            idx_map.insert(s.to_string(), idx1);
                        }
                    }
                }
                dag.add_edge(idx, idx1, true);
                match c2 {
                    Node::And(_) => {
                        idx2 = dag.add_node(DagNode::Intersec(IntersecNode {}));
                    }
                    Node::Or(_) => {
                        idx2 = dag.add_node(DagNode::Union(UnionNode {}));
                    }
                    Node::Not(_) => {
                        idx2 = dag.add_node(DagNode::Diff(DiffNode {}));
                    }
                    Node::Input(s) => {
                        if let Some(c_idx) = idx_map.get(s) {
                            idx2 = *c_idx;
                        } else {
                            idx2 = dag.add_node(DagNode::Keyword(Box::new(KeywordNode {
                                keyword: s.to_string(),
                            })));
                            idx_map.insert(s.to_string(), idx2);
                        }
                    }
                }
                dag.add_edge(idx, idx2, false);
                queue.push_back((c1, idx1));
                queue.push_back((c2, idx2));
            }
            Node::Not(n) => {
                let NotNode(c) = n.as_ref();
                let c_idx: NodeIndex;
                let blk_rt_idx = dag.add_node(DagNode::BlkRt(Box::new(BlkRtNode {})));
                match c {
                    Node::And(_) => {
                        c_idx = dag.add_node(DagNode::Intersec(IntersecNode {}));
                    }
                    Node::Or(_) => {
                        c_idx = dag.add_node(DagNode::Union(UnionNode {}));
                    }
                    Node::Not(_) => {
                        c_idx = dag.add_node(DagNode::Diff(DiffNode {}));
                    }
                    Node::Input(s) => {
                        if let Some(ch_idx) = idx_map.get(s) {
                            c_idx = *ch_idx;
                        } else {
                            c_idx = dag.add_node(DagNode::Keyword(Box::new(KeywordNode {
                                keyword: s.to_string(),
                            })));
                            idx_map.insert(s.to_string(), c_idx);
                        }
                    }
                }
                dag.add_edge(idx, c_idx, true);
                dag.add_edge(idx, blk_rt_idx, false);
                queue.push_back((c, c_idx));
            }
            Node::Input(_) => {}
        }
    }
    Ok(keyword_root_idx)
}

pub fn gen_parallel_query_dag<K: Num>(
    query_content: &QueryContent<K>,
) -> Result<Graph<DagNode<K>, bool>> {
    let keyword_exp_opt = query_content.keyword_exp.as_ref();
    let mut query_dag = Graph::<DagNode<K>, bool>::new();
    let mut keyword_root_idx: NodeIndex = NodeIndex::default();
    let mut range_root_idx: NodeIndex = NodeIndex::default();
    let has_keyword_query: bool;
    let has_range_query: bool;

    if let Some(keyword_exp) = keyword_exp_opt.as_ref() {
        has_keyword_query = true;
        keyword_root_idx = query_dag_add_keyword_exp(keyword_exp, &mut query_dag)?;
    } else {
        has_keyword_query = false;
    }

    if !query_content.range.is_empty() {
        has_range_query = true;
        let mut range_lock = false;
        for (i, r) in query_content.range.iter().enumerate() {
            // add range
            let range_idx = query_dag.add_node(DagNode::Range(RangeNode { range: *r, dim: i }));
            if range_lock {
                // add intersec
                let intersec_idx = query_dag.add_node(DagNode::Intersec(IntersecNode {}));
                query_dag.add_edge(intersec_idx, range_root_idx, true);
                query_dag.add_edge(intersec_idx, range_idx, false);
                range_root_idx = intersec_idx;
                continue;
            }
            range_root_idx = range_idx;
            range_lock = true;
        }
    } else {
        has_range_query = false;
    }

    let root_idx;
    if has_keyword_query && has_range_query {
        root_idx = query_dag.add_node(DagNode::Intersec(IntersecNode {}));
        query_dag.add_edge(root_idx, range_root_idx, true);
        query_dag.add_edge(root_idx, keyword_root_idx, false);
    }

    Ok(query_dag)
}

#[allow(clippy::type_complexity)]
pub fn gen_last_query_dag_with_cont_basic<K: Num>(
    time_win: &TimeWin,
    s_win_size: Option<u64>,
    mut query_dag: Graph<DagNode<K>, bool>,
) -> Result<(Graph<DagNode<K>, bool>, QueryPlan<K>)> {
    let end_blk_height = Height(time_win.end_blk);
    let mut dag_content = HashMap::<NodeIndex, QPNode<K>>::new();
    let mut root_idx;
    // process end sub_dag
    let mut end_q_inputs = match toposort(&query_dag, None) {
        Ok(v) => v,
        Err(_) => {
            bail!("Input query graph not valid")
        }
    };
    end_q_inputs.reverse();
    let end_sub_root_idx = end_q_inputs.last().context("empty dag")?;
    root_idx = *end_sub_root_idx;

    for idx in &end_q_inputs {
        if let Some(dag_node) = query_dag.node_weight(*idx) {
            match dag_node {
                DagNode::Range(_) => {
                    let qp_range_node = QPRangeNode {
                        blk_height: end_blk_height,
                        set: None,
                    };
                    dag_content.insert(*idx, QPNode::Range(qp_range_node));
                }
                DagNode::Keyword(_) => {
                    let qp_keyword_node = QPKeywordNode {
                        blk_height: end_blk_height,
                        set: None,
                    };
                    dag_content.insert(*idx, QPNode::Keyword(Box::new(qp_keyword_node)));
                }
                DagNode::BlkRt(_) => {
                    let qp_rt_node = QPBlkRtNode {
                        blk_height: end_blk_height,
                        set: None,
                    };
                    dag_content.insert(*idx, QPNode::BlkRt(Box::new(qp_rt_node)));
                }
                DagNode::Union(_) => {
                    let qp_union_node = QPUnion { set: None };
                    dag_content.insert(*idx, QPNode::Union(qp_union_node));
                }
                DagNode::Intersec(_) => {
                    let qp_intersec_node = QPIntersec { set: None };
                    dag_content.insert(*idx, QPNode::Intersec(qp_intersec_node));
                }
                DagNode::Diff(_) => {
                    let qp_diff_node = QPDiff { set: None };
                    dag_content.insert(*idx, QPNode::Diff(qp_diff_node));
                }
            }
        }
    }

    // process start sub_dag
    if s_win_size.is_some() && time_win.start_blk > 1 {
        let start_blk_height = Height(time_win.start_blk - 1);
        let start_sub_root_idx = query_dag.add_node(DagNode::BlkRt(Box::new(BlkRtNode {})));
        let qp_rt_node = QPBlkRtNode {
            blk_height: start_blk_height,
            set: None,
        };
        dag_content.insert(start_sub_root_idx, QPNode::BlkRt(Box::new(qp_rt_node)));
        let diff_idx = query_dag.add_node(DagNode::Diff(DiffNode {}));
        query_dag.add_edge(diff_idx, start_sub_root_idx, true);
        query_dag.add_edge(diff_idx, *end_sub_root_idx, false);
        dag_content.insert(diff_idx, QPNode::Diff(QPDiff { set: None }));
        root_idx = diff_idx;
    }

    let qp_root_idx = root_idx;
    let qp = QueryPlan {
        end_blk_height,
        root_idx: qp_root_idx,
        dag_content,
        trie_proofs: HashMap::new(),
    };

    Ok((query_dag, qp))
}

#[allow(clippy::type_complexity)]
pub fn gen_last_query_dag_with_cont_trimmed<K: Num, T: ReadInterface<K = K>>(
    time_win: &TimeWin,
    s_win_size: Option<u64>,
    e_win_size: u64,
    mut query_dag: Graph<DagNode<K>, bool>,
    query_content: &QueryContent<K>,
    chain: &T,
    pk: &AccPublicKey,
) -> Result<(Graph<DagNode<K>, bool>, QueryPlan<K>)> {
    let end_blk_height = Height(time_win.end_blk);
    let mut dag_content = HashMap::<NodeIndex, QPNode<K>>::new();
    let mut trie_ctxes = HashMap::<Height, trie_tree::read::ReadContext<T>>::new();
    let mut root_idx;
    // process end sub_dag
    let mut end_q_inputs = match toposort(&query_dag, None) {
        Ok(v) => v,
        Err(_) => {
            bail!("Input query graph not valid")
        }
    };
    end_q_inputs.reverse();
    let end_sub_root_idx = end_q_inputs.last().context("empty dag")?;
    root_idx = *end_sub_root_idx;

    for idx in &end_q_inputs {
        if let Some(dag_node) = query_dag.node_weight(*idx) {
            match dag_node {
                DagNode::Range(node) => {
                    let bplus_root = chain
                        .read_block_content(end_blk_height)?
                        .ads
                        .read_bplus_root(e_win_size, node.dim)?;
                    let (s, a, p) = bplus_tree::read::range_query(
                        chain,
                        bplus_root.bplus_tree_root_id,
                        node.range,
                        pk,
                    )?;
                    let qp_range_node = QPRangeNode {
                        blk_height: end_blk_height,
                        set: Some((s, a, p)),
                    };
                    dag_content.insert(*idx, QPNode::Range(qp_range_node));
                }
                DagNode::Keyword(node) => {
                    let set;
                    let acc;
                    if let Some(ctx) = trie_ctxes.get_mut(&end_blk_height) {
                        let (s, a) = ctx.query(&SmolStr::from(&node.keyword), pk)?;
                        set = s;
                        acc = a;
                    } else {
                        let trie_root = chain
                            .read_block_content(end_blk_height)?
                            .ads
                            .read_trie_root(e_win_size)?;
                        let mut trie_ctx =
                            trie_tree::read::ReadContext::new(chain, trie_root.trie_root_id);
                        let (s, a) = trie_ctx.query(&SmolStr::from(&node.keyword), pk)?;
                        set = s;
                        acc = a;
                        trie_ctxes.insert(end_blk_height, trie_ctx);
                    }
                    let qp_keyword_node = QPKeywordNode {
                        blk_height: end_blk_height,
                        set: Some((set, acc)),
                    };
                    dag_content.insert(*idx, QPNode::Keyword(Box::new(qp_keyword_node)));
                }
                DagNode::BlkRt(_) => {
                    let set;
                    let acc;
                    let blk_content = chain.read_block_content(end_blk_height)?;
                    let bplus_root = blk_content.ads.read_bplus_root(e_win_size, 0)?;
                    let bplus_root_id =
                        bplus_root.bplus_tree_root_id.context("Empty bplus root")?;
                    let bplus_root_node =
                        bplus_tree::BPlusTreeNodeLoader::load_node(chain, bplus_root_id)?;
                    set = bplus_root_node.get_set().clone();
                    acc = bplus_root_node.get_node_acc();
                    let qp_rt_node = QPBlkRtNode {
                        blk_height: end_blk_height,
                        set: Some((set, acc)),
                    };
                    dag_content.insert(*idx, QPNode::BlkRt(Box::new(qp_rt_node)));
                }
                DagNode::Union(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for c_idx in query_dag.neighbors_directed(*idx, Outgoing) {
                        child_idxs.push(c_idx);
                    }
                    let qp_c_idx1 = child_idxs
                        .get(0)
                        .context("Cannot find the first qp child idx of union")?;
                    let qp_c1 = dag_content
                        .get(qp_c_idx1)
                        .context("Cannot find the first child vo node in vo_dag_content")?;
                    let c1_set = qp_c1.get_set()?;
                    let qp_c_idx2 = child_idxs
                        .get(1)
                        .context("Cannot find the second qp child idx of union")?;
                    let qp_c2 = dag_content
                        .get(qp_c_idx2)
                        .context("Cannot find the second child vo node in vo_dag_content")?;
                    let c2_set = qp_c2.get_set()?;
                    let c_union = c1_set | c2_set;
                    let qp_union_node = QPUnion {
                        set: Some((c_union, 0, 0)),
                    };
                    dag_content.insert(*idx, QPNode::Union(qp_union_node));
                }
                DagNode::Intersec(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for c_idx in query_dag.neighbors_directed(*idx, Outgoing) {
                        child_idxs.push(c_idx);
                    }
                    let qp_c_idx1 = child_idxs
                        .get(0)
                        .context("Cannot find the first qp child idx of union")?;
                    let qp_c1 = dag_content
                        .get(qp_c_idx1)
                        .context("Cannot find the first child vo node in vo_dag_content")?;
                    let c1_set = qp_c1.get_set()?;
                    let qp_c_idx2 = child_idxs
                        .get(1)
                        .context("Cannot find the second qp child idx of union")?;
                    let qp_c2 = dag_content
                        .get(qp_c_idx2)
                        .context("Cannot find the second child vo node in vo_dag_content")?;
                    let c2_set = qp_c2.get_set()?;
                    let c_intersec = c1_set & c2_set;
                    let qp_intersec_node = QPIntersec {
                        set: Some((c_intersec, 0, 0)),
                    };
                    dag_content.insert(*idx, QPNode::Intersec(qp_intersec_node));
                }
                DagNode::Diff(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for c_idx in query_dag.neighbors_directed(*idx, Outgoing) {
                        child_idxs.push(c_idx);
                    }
                    let mut qp_c_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first qp child idx of difference")?;
                    let qp_c_idx2;
                    let edge_idx = query_dag
                        .find_edge(*idx, *qp_c_idx1)
                        .context("Cannot find edge")?;
                    let weight = query_dag
                        .edge_weight(edge_idx)
                        .context("Cannot find edge")?;
                    if !*weight {
                        qp_c_idx2 = child_idxs
                            .get(0)
                            .context("Cannot find the first qp child idx of difference")?;
                    } else {
                        qp_c_idx1 = child_idxs
                            .get(0)
                            .context("Cannot find the first qp child idx of difference")?;
                        qp_c_idx2 = child_idxs
                            .get(1)
                            .context("Cannot find the first qp child idx of difference")?;
                    }
                    let qp_c1 = dag_content
                        .get(qp_c_idx1)
                        .context("Cannot find the first child vo node in vo_dag_content")?;
                    let c1_set = qp_c1.get_set()?;
                    let qp_c2 = dag_content
                        .get(qp_c_idx2)
                        .context("Cannot find the second child vo node in vo_dag_content")?;
                    let c2_set = qp_c2.get_set()?;
                    let c_diff = c1_set / c2_set;
                    let qp_diff_node = QPDiff {
                        set: Some((c_diff, 0, 0)),
                    };
                    dag_content.insert(*idx, QPNode::Diff(qp_diff_node));
                }
            }
        }
    }

    let end_blk_res_size = dag_content
        .get(end_sub_root_idx)
        .context("root does not exist")?
        .get_set()?
        .len();

    // process start sub_dag
    if let Some(s_win_size) = s_win_size {
        if time_win.start_blk > 1 {
            let start_blk_height = Height(time_win.start_blk - 1);
            let mut start_sub_root_idx: NodeIndex = NodeIndex::default();
            let keyword_exp_opt = query_content.keyword_exp.as_ref();
            let has_range_query: bool;
            if query_content.range.is_empty() {
                has_range_query = false;
            } else {
                has_range_query = true;
            }
            let trie_root = chain
                .read_block_content(start_blk_height)?
                .ads
                .read_trie_root(s_win_size)?;
            let mut trie_ctx = trie_tree::read::ReadContext::new(chain, trie_root.trie_root_id);
            let mut sub_graphs = Vec::<(
                usize,
                NodeIndex,
                Graph<DagNode<K>, bool>,
                HashMap<NodeIndex, QPNode<K>>,
            )>::new();

            if let Some(keyword_exp) = keyword_exp_opt {
                let k_exp_set = keyword_exp.to_cnf_set();
                for k_exp in &k_exp_set {
                    let (cost, sub_rt_idx, sub_graph, sub_content) = process_keyword_sub_node(
                        k_exp,
                        start_blk_height,
                        s_win_size,
                        &mut trie_ctx,
                        chain,
                        pk,
                    )?;
                    sub_graphs.push((cost, sub_rt_idx, sub_graph, sub_content));
                }
                trie_ctxes.insert(start_blk_height, trie_ctx);
            }

            if has_range_query {
                for (i, r) in query_content.range.iter().enumerate() {
                    let range_node = RangeNode { range: *r, dim: i };
                    let bplus_root = chain
                        .read_block_content(start_blk_height)?
                        .ads
                        .read_bplus_root(s_win_size, i)?;
                    let (s, a, p) = bplus_tree::read::range_query(
                        chain,
                        bplus_root.bplus_tree_root_id,
                        *r,
                        pk,
                    )?;
                    let qp_range_node = QPRangeNode {
                        blk_height: start_blk_height,
                        set: Some((s, a, p)),
                    };
                    let mut sub_graph = Graph::<DagNode<K>, bool>::new();
                    let rt_idx = sub_graph.add_node(DagNode::Range(range_node));
                    let mut sub_content = HashMap::new();
                    sub_content.insert(rt_idx, QPNode::Range(qp_range_node));
                    sub_graphs.push((0, rt_idx, sub_graph, sub_content));
                }
            }

            sub_graphs.sort_by(|a, b| a.0.cmp(&b.0));
            let mut cur_cost = std::usize::MAX;
            let mut lock = false;
            let mut pre_set = Set::new();
            let mut pre_set_len = 0;
            let mut intersec: Set;
            for (sub_cost, sub_rt_idx, sub_graph, sub_content) in &mut sub_graphs {
                let cur_set = sub_content.get(sub_rt_idx).context("")?.get_set()?;
                if !lock {
                    cur_cost = *sub_cost + cur_set.len() * end_blk_res_size;
                    pre_set = cur_set.clone();
                    pre_set_len = pre_set.len();
                    start_sub_root_idx = combine_query_dags(
                        &mut query_dag,
                        &mut dag_content,
                        sub_graph,
                        sub_content,
                        *sub_rt_idx,
                    )?;
                    lock = true;
                } else {
                    let cur_set_len = cur_set.len();
                    intersec = (&pre_set) & cur_set;
                    let cost = pre_set_len * cur_set_len * COST_COEFFICIENT
                        + intersec.len() * end_blk_res_size;
                    if cost >= cur_cost {
                        break;
                    } else {
                        cur_cost = cost;
                        pre_set = intersec;
                        pre_set_len = pre_set.len();
                        start_sub_root_idx = combine_query_dags_by_intersec(
                            &mut query_dag,
                            start_sub_root_idx,
                            &mut dag_content,
                            sub_graph,
                            *sub_rt_idx,
                            sub_content,
                        )?;
                    }
                }
            }
            let diff_idx = query_dag.add_node(DagNode::Diff(DiffNode {}));
            query_dag.add_edge(diff_idx, start_sub_root_idx, true);
            query_dag.add_edge(diff_idx, *end_sub_root_idx, false);
            dag_content.insert(diff_idx, QPNode::Diff(QPDiff { set: None }));
            root_idx = diff_idx;
        }
    }
    let mut trie_proofs = HashMap::new();
    for (h, trie_ctx) in trie_ctxes {
        trie_proofs.insert(h, trie_ctx.into_proof());
    }
    let qp_root_idx = root_idx;
    let qp = QueryPlan {
        end_blk_height,
        root_idx: qp_root_idx,
        dag_content,
        trie_proofs,
    };

    Ok((query_dag, qp))
}

#[allow(clippy::type_complexity)]
fn process_keyword_sub_node<K: Num, T: ReadInterface<K = K>>(
    sub_exp: &Node,
    blk_height: Height,
    win_size: u64,
    trie_ctx: &mut trie_tree::read::ReadContext<T>,
    chain: &T,
    pk: &AccPublicKey,
) -> Result<(
    usize,
    NodeIndex,
    Graph<DagNode<K>, bool>,
    HashMap<NodeIndex, QPNode<K>>,
)> {
    let mut sub_dag = Graph::<DagNode<K>, bool>::new();
    let sub_root_idx = query_dag_add_keyword_exp(sub_exp, &mut sub_dag)?;

    let mut inputs = match toposort(&sub_dag, None) {
        Ok(v) => v,
        Err(_) => {
            bail!("Input query plan graph not valid")
        }
    };
    inputs.reverse();
    let mut dag_content = HashMap::new();
    let cost = estimate_keyword_sub_dag_cost(
        &inputs,
        &mut sub_dag,
        &mut dag_content,
        trie_ctx,
        blk_height,
        win_size,
        chain,
        pk,
    )?;

    Ok((cost, sub_root_idx, sub_dag, dag_content))
}

#[allow(clippy::too_many_arguments)]
fn estimate_keyword_sub_dag_cost<K: Num, T: ReadInterface<K = K>>(
    inputs: &[NodeIndex],
    dag: &mut Graph<DagNode<K>, bool>,
    dag_content: &mut HashMap<NodeIndex, QPNode<K>>,
    trie_ctx: &mut trie_tree::read::ReadContext<T>,
    blk_height: Height,
    win_size: u64,
    chain: &T,
    pk: &AccPublicKey,
) -> Result<usize> {
    let mut cost: usize = 0;
    for idx in inputs {
        if let Some(node) = dag.node_weight_mut(*idx) {
            match node {
                DagNode::Range(n) => {
                    let bplus_root = chain
                        .read_block_content(blk_height)?
                        .ads
                        .read_bplus_root(win_size, n.dim)?;
                    let (s, a, p) = bplus_tree::read::range_query(
                        chain,
                        bplus_root.bplus_tree_root_id,
                        n.range,
                        pk,
                    )?;
                    let qp_range_node = QPRangeNode {
                        blk_height,
                        set: Some((s, a, p)),
                    };
                    dag_content.insert(*idx, QPNode::Range(qp_range_node));
                }
                DagNode::Keyword(n) => {
                    let (s, a) = trie_ctx.query(&SmolStr::from(&n.keyword), pk)?;
                    let qp_keyword_node = QPKeywordNode {
                        blk_height,
                        set: Some((s, a)),
                    };
                    dag_content.insert(*idx, QPNode::Keyword(Box::new(qp_keyword_node)));
                }
                DagNode::BlkRt(_) => {
                    let blk_content = chain.read_block_content(Height(blk_height.0))?;
                    let bplus_root = blk_content.ads.read_bplus_root(win_size, 0)?;
                    let bplus_root_id =
                        bplus_root.bplus_tree_root_id.context("Empty bplus root")?;
                    let bplus_root_node =
                        bplus_tree::BPlusTreeNodeLoader::load_node(chain, bplus_root_id)?;
                    let set = bplus_root_node.get_set().clone();
                    let acc = bplus_root_node.get_node_acc();
                    let qp_blk_rt_node = QPBlkRtNode {
                        blk_height,
                        set: Some((set, acc)),
                    };
                    dag_content.insert(*idx, QPNode::BlkRt(Box::new(qp_blk_rt_node)));
                }
                DagNode::Union(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for index in dag.neighbors_directed(*idx, Outgoing) {
                        child_idxs.push(index);
                    }
                    let q_c_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first child idx of union")?;
                    let q_c1 = dag_content
                        .get(q_c_idx1)
                        .context("Cannot find the first child node in dag_content")?;
                    let s1 = q_c1.get_set()?;
                    let q_c_idx2 = child_idxs
                        .get(0)
                        .context("Cannot find the first child idx of union")?;
                    let q_c2 = dag_content
                        .get(q_c_idx2)
                        .context("Cannot find the second child node in dag_content")?;
                    let s2 = q_c2.get_set()?;
                    let res_set = (s1) | (s2);
                    let inter_cost = COST_COEFFICIENT * s1.len() * s2.len();
                    cost += inter_cost;
                    let qp_union_node = QPUnion {
                        set: Some((res_set, 0, 0)),
                    };
                    dag_content.insert(*idx, QPNode::Union(qp_union_node));
                }
                DagNode::Intersec(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for index in dag.neighbors_directed(*idx, Outgoing) {
                        child_idxs.push(index);
                    }
                    let q_c_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first child idx of intersection")?;
                    let q_c1 = dag_content
                        .get(q_c_idx1)
                        .context("Cannot find the first child node in dag_content")?;
                    let s1 = q_c1.get_set()?;
                    let q_c_idx2 = child_idxs
                        .get(0)
                        .context("Cannot find the first child idx of intersection")?;
                    let q_c2 = dag_content
                        .get(q_c_idx2)
                        .context("Cannot find the second child node in dag_content")?;
                    let s2 = q_c2.get_set()?;
                    let res_set = (s1) & (s2);
                    let inter_cost = COST_COEFFICIENT * s1.len() * s2.len();
                    cost += inter_cost;
                    let qp_intersec_node = QPIntersec {
                        set: Some((res_set, 0, 0)),
                    };
                    dag_content.insert(*idx, QPNode::Intersec(qp_intersec_node));
                }
                DagNode::Diff(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for index in dag.neighbors_directed(*idx, Outgoing) {
                        child_idxs.push(index);
                    }
                    let mut qp_c_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first qp child idx of difference")?;
                    let qp_c_idx2;
                    let edge_idx = dag
                        .find_edge(*idx, *qp_c_idx1)
                        .context("Cannot find edge")?;
                    let weight = dag.edge_weight(edge_idx).context("Cannot find edge")?;
                    if !*weight {
                        qp_c_idx2 = child_idxs
                            .get(0)
                            .context("Cannot find the first qp child idx of difference")?;
                    } else {
                        qp_c_idx1 = child_idxs
                            .get(0)
                            .context("Cannot find the first qp child idx of difference")?;
                        qp_c_idx2 = child_idxs
                            .get(1)
                            .context("Cannot find the first qp child idx of difference")?;
                    }
                    let qp_c1 = dag_content
                        .get(qp_c_idx1)
                        .context("Cannot find the first child vo node in vo_dag_content")?;
                    let s1 = qp_c1.get_set()?;
                    let qp_c2 = dag_content
                        .get(qp_c_idx2)
                        .context("Cannot find the second child vo node in vo_dag_content")?;
                    let s2 = qp_c2.get_set()?;
                    let c_diff = s1 / s2;
                    let inter_cost = COST_COEFFICIENT * s1.len() * s2.len();
                    cost += inter_cost;
                    let qp_diff_node = QPDiff {
                        set: Some((c_diff, 0, 0)),
                    };
                    dag_content.insert(*idx, QPNode::Diff(qp_diff_node));
                }
            }
        }
    }

    Ok(cost)
}

fn combine_query_dags<K: Num>(
    graph1: &mut Graph<DagNode<K>, bool>,
    content1: &mut HashMap<NodeIndex, QPNode<K>>,
    graph2: &mut Graph<DagNode<K>, bool>,
    content2: &mut HashMap<NodeIndex, QPNode<K>>,
    graph2_root_idx: NodeIndex,
) -> Result<NodeIndex> {
    // store old-new idx pairs
    let mut old_new_idx = HashMap::<NodeIndex, NodeIndex>::new();
    // store old graph edge info
    let mut old_edges = Vec::<(NodeIndex, NodeIndex, bool)>::new();

    let graph2_idxes = graph2.node_indices();
    for idx in graph2_idxes.rev() {
        for c_idx in graph2.neighbors_directed(idx, Outgoing) {
            let edge_idx = graph2.find_edge(idx, c_idx).context("Cannot find edge")?;
            let weight = graph2.edge_weight(edge_idx).context("Cannot find edge")?;
            old_edges.push((idx, c_idx, *weight));
        }
        for p_idx in graph2.neighbors_directed(idx, Incoming) {
            let edge_idx = graph2.find_edge(p_idx, idx).context("Cannot find edge")?;
            let weight = graph2.edge_weight(edge_idx).context("Cannot find edge")?;
            old_edges.push((p_idx, idx, *weight));
        }
        let node = graph2.remove_node(idx).context("Node does not exist")?;
        let new_idx = graph1.add_node(node);
        let qp_node = content2
            .remove(&idx)
            .context("QPNode does not exist in old dag_cont")?;
        content1.insert(new_idx, qp_node);
        old_new_idx.insert(idx, new_idx);
    }
    for (old_s, old_e, weight) in old_edges.iter().rev() {
        let new_s = old_new_idx.get(old_s).context("Cannot find idx in map")?;
        let new_e = old_new_idx.get(old_e).context("Cannot find idx in map")?;
        graph1.add_edge(*new_s, *new_e, *weight);
    }
    let sub_root = old_new_idx
        .get(&graph2_root_idx)
        .context("Cannot find graph2 root index")?;
    Ok(*sub_root)
}

fn combine_query_dags_by_intersec<K: Num>(
    graph1: &mut Graph<DagNode<K>, bool>,
    graph1_root_idx: NodeIndex,
    content1: &mut HashMap<NodeIndex, QPNode<K>>,
    graph2: &mut Graph<DagNode<K>, bool>,
    graph2_root_idx: NodeIndex,
    content2: &mut HashMap<NodeIndex, QPNode<K>>,
) -> Result<NodeIndex> {
    let new_graph2_sub_root_idx =
        combine_query_dags(graph1, content1, graph2, content2, graph2_root_idx)?;
    let s1 = content1
        .get(&graph1_root_idx)
        .context("Cannot find subroot1")?
        .get_set()?;
    let s2 = content1
        .get(&new_graph2_sub_root_idx)
        .context("Cannot find subroot1")?
        .get_set()?;
    let s_new = s1 & s2;
    let new_root_idx = graph1.add_node(DagNode::Intersec(IntersecNode {}));
    graph1.add_edge(new_root_idx, graph1_root_idx, true);
    graph1.add_edge(new_root_idx, new_graph2_sub_root_idx, false);
    let qp_intersec_node = QPIntersec {
        set: Some((s_new, 0, 0)),
    };
    content1.insert(new_root_idx, QPNode::Intersec(qp_intersec_node));

    Ok(new_root_idx)
}
