use crate::{
    acc::{AccPublicKey, Set},
    chain::{
        block::Height,
        query::query_obj::{
            estimate_query_cost, BlkRtNode, DiffNode, IntersecNode, KeywordNode, Query, QueryNode,
            RangeNode, UnionNode,
        },
        range::Range,
        traits::{Num, ReadInterface},
        trie_tree,
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
use std::collections::{HashMap, HashSet, VecDeque};

use super::{QueryContent, TimeWin};

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Node {
    And(Box<AndNode>),
    Or(Box<OrNode>),
    Not(Box<NotNode>),
    Input(String),
}

impl Node {
    pub fn set_to_cnf(cnf_set: &HashSet<Self>) -> Self {
        let mut lock = false;
        let mut node = Node::Input("init".to_string());
        for s in cnf_set {
            if lock {
                node = Node::And(Box::new(AndNode(node, s.clone())));
            } else {
                node = s.clone();
                lock = true;
            }
        }
        node
    }
    pub fn to_cnf_set(&self) -> HashSet<Self> {
        match self {
            Node::And(n) => {
                let AndNode(c1, c2) = n.as_ref();
                let c1_set = c1.to_cnf_set();
                let c2_set = c2.to_cnf_set();
                let res: HashSet<Node> = c1_set.union(&c2_set).cloned().collect();
                res
            }
            Node::Or(n) => {
                let OrNode(c1, c2) = n.as_ref();
                let c1_set = c1.to_cnf_set();
                let c2_set = c2.to_cnf_set();
                let mut res = HashSet::<Node>::new();
                for c1_n in &c1_set {
                    for c2_n in &c2_set {
                        res.insert(Node::Or(Box::new(OrNode(c1_n.clone(), c2_n.clone()))));
                    }
                }
                res
            }
            Node::Not(n) => {
                let NotNode(c) = n.as_ref();
                match c {
                    Node::And(c_n) => {
                        let AndNode(c_c_1, c_c_2) = c_n.as_ref();
                        let exp = Node::Or(Box::new(OrNode(
                            Node::Not(Box::new(NotNode(c_c_1.clone()))),
                            Node::Not(Box::new(NotNode(c_c_2.clone()))),
                        )));
                        exp.to_cnf_set()
                    }
                    Node::Or(c_n) => {
                        let OrNode(c_c_1, c_c_2) = c_n.as_ref();
                        let exp = Node::And(Box::new(AndNode(
                            Node::Not(Box::new(NotNode(c_c_1.clone()))),
                            Node::Not(Box::new(NotNode(c_c_2.clone()))),
                        )));
                        exp.to_cnf_set()
                    }
                    Node::Not(c_n) => {
                        let NotNode(inner) = c_n.as_ref();
                        inner.to_cnf_set()
                    }
                    Node::Input(_) => {
                        let mut res = HashSet::<Node>::new();
                        res.insert(Node::Not(n.clone()));
                        res
                    }
                }
            }
            Node::Input(n) => {
                let mut res = HashSet::<Node>::new();
                res.insert(Node::Input(n.to_string()));
                res
            }
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct AndNode(pub Node, pub Node);

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct OrNode(pub Node, pub Node);

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct NotNode(pub Node);

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct QueryParam<K: Num> {
    pub start_blk: u64,
    pub end_blk: u64,
    pub range: Vec<Range<K>>,
    pub keyword_exp: Option<Node>,
}

impl<K: Num> QueryParam<K> {
    pub fn get_start(&self) -> u64 {
        self.start_blk
    }

    pub fn get_end(&self) -> u64 {
        self.end_blk
    }

    pub fn gen_time_win(&self) -> TimeWin {
        TimeWin {
            start_blk: self.start_blk,
            end_blk: self.end_blk,
        }
    }

    pub fn gen_query_content(&self) -> QueryContent<K> {
        QueryContent {
            range: self.range.clone(),
            keyword_exp: self.keyword_exp.clone(),
        }
    }
}

#[allow(clippy::type_complexity)]
pub fn param_to_query_basic<K: Num>(
    time_win: TimeWin,
    query_content: &QueryContent<K>,
    start_win_size: Option<u64>,
    end_win_size: u64,
) -> Result<Query<K>> {
    let end_blk_height = Height(time_win.end_blk);
    let keyword_exp_opt = query_content.keyword_exp.as_ref();
    let mut query_dag = Graph::<QueryNode<K>, bool>::new();

    let mut keyword_root_idx: NodeIndex = NodeIndex::default();
    let mut range_root_idx: NodeIndex = NodeIndex::default();
    let has_keyword_query: bool;
    let has_range_query: bool;

    if let Some(keyword_exp) = keyword_exp_opt.as_ref() {
        has_keyword_query = true;
        keyword_root_idx =
            dag_add_keyword_exp(keyword_exp, &mut query_dag, end_blk_height, end_win_size)?;
    } else {
        has_keyword_query = false;
    }

    if !query_content.range.is_empty() {
        has_range_query = true;
        let mut range_lock = false;
        for (i, r) in query_content.range.iter().enumerate() {
            // add range
            let range_idx = query_dag.add_node(QueryNode::Range(RangeNode {
                range: *r,
                blk_height: end_blk_height,
                time_win: end_win_size,
                dim: i,
                set: None,
            }));
            if range_lock {
                // add intersec
                let intersec_idx =
                    query_dag.add_node(QueryNode::Intersec(IntersecNode { set: None }));
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

    let end_blk_idx: NodeIndex;

    if has_keyword_query && has_range_query {
        debug!("has both keyword and range query");
        end_blk_idx = query_dag.add_node(QueryNode::Intersec(IntersecNode { set: None }));
        query_dag.add_edge(end_blk_idx, range_root_idx, true);
        query_dag.add_edge(end_blk_idx, keyword_root_idx, false);
    } else if has_keyword_query {
        debug!("has keyword query only");
        end_blk_idx = keyword_root_idx;
    } else if has_range_query {
        debug!("has range query only");
        end_blk_idx = range_root_idx;
    } else {
        debug!("invalid query");
        bail!("query invalid");
    }

    if let Some(size) = start_win_size {
        if time_win.start_blk > 1 {
            let blk_rt_idx = query_dag.add_node(QueryNode::BlkRt(Box::new(BlkRtNode {
                blk_height: Height(time_win.start_blk - 1),
                time_win: size,
                set: None,
            })));
            let diff_idx = query_dag.add_node(QueryNode::Diff(DiffNode { set: None }));
            query_dag.add_edge(diff_idx, blk_rt_idx, true);
            query_dag.add_edge(diff_idx, end_blk_idx, false);
        }
    }
    let res_query = Query {
        end_blk_height,
        query_dag,
        trie_proofs: HashMap::<Height, trie_tree::proof::Proof>::new(),
    };
    Ok(res_query)
}

pub fn param_to_query_trimmed<K: Num, T: ReadInterface<K = K>>(
    time_win: TimeWin,
    query_content: &QueryContent<K>,
    chain: &T,
    pk: &AccPublicKey,
    start_win_size: Option<u64>,
    end_win_size: u64,
) -> Result<Query<K>> {
    // query at start point, without any planning
    let start_blk_height = Height(time_win.start_blk);
    let end_blk_height = Height(time_win.end_blk);
    let keyword_exp_opt = query_content.keyword_exp.as_ref();
    let mut query_dag = Graph::<QueryNode<K>, bool>::new();
    let mut heights = Vec::<(u64, Height)>::new();
    if let Some(win_size) = start_win_size {
        if start_blk_height.0 > 1 {
            heights.push((win_size, Height(start_blk_height.0 - 1)));
        }
    }
    heights.push((end_win_size, end_blk_height));
    debug!("heights: {:?}", heights);

    let has_keyword_query: bool;
    let has_range_query: bool;

    match keyword_exp_opt {
        Some(_) => has_keyword_query = true,
        None => has_keyword_query = false,
    }

    if query_content.range.is_empty() {
        has_range_query = false;
    } else {
        has_range_query = true;
    }

    let mut sub_root_idxes = Vec::<NodeIndex>::new();
    for (win_size, height) in heights {
        let mut keyword_root_idx: NodeIndex = NodeIndex::default();
        let mut range_root_idx: NodeIndex = NodeIndex::default();

        if let Some(keyword_exp) = keyword_exp_opt.as_ref() {
            keyword_root_idx = dag_add_keyword_exp(keyword_exp, &mut query_dag, height, win_size)?;
        }

        if has_range_query {
            let mut range_nodes = Vec::<(usize, NodeIndex, Set)>::new();
            for (i, r) in query_content.range.iter().enumerate() {
                let mut range_node = RangeNode {
                    range: *r,
                    blk_height: height,
                    time_win: win_size,
                    dim: i,
                    set: None,
                };
                range_node.estimate_size(chain, pk)?;
                let set = range_node.set.as_ref().context("No set found")?.0.clone();
                let range_size = set.len();
                let range_idx = query_dag.add_node(QueryNode::Range(range_node));
                range_nodes.push((range_size, range_idx, set));
            }
            let sorted_idxes = get_range_idxs_sorted(range_nodes);
            let mut range_lock = false;
            for idx in sorted_idxes {
                if range_lock {
                    let intersec_idx =
                        query_dag.add_node(QueryNode::Intersec(IntersecNode { set: None }));
                    query_dag.add_edge(intersec_idx, range_root_idx, true);
                    query_dag.add_edge(intersec_idx, idx, false);
                    range_root_idx = intersec_idx;
                    continue;
                }
                range_root_idx = idx;
                range_lock = true;
            }
        }
        let sub_root_idx: NodeIndex;

        if has_keyword_query && has_range_query {
            debug!("has both keyword and range query");
            sub_root_idx = query_dag.add_node(QueryNode::Intersec(IntersecNode { set: None }));
            query_dag.add_edge(sub_root_idx, range_root_idx, true);
            query_dag.add_edge(sub_root_idx, keyword_root_idx, false);
        } else if has_keyword_query {
            debug!("has keyword query only");
            sub_root_idx = keyword_root_idx;
        } else if has_range_query {
            debug!("has range query only");
            sub_root_idx = range_root_idx;
        } else {
            debug!("invalid query");
            bail!("query invalid");
        }
        sub_root_idxes.push(sub_root_idx);
    }
    if sub_root_idxes.len() > 1 {
        let diff_idx = query_dag.add_node(QueryNode::Diff(DiffNode { set: None }));
        query_dag.add_edge(diff_idx, *sub_root_idxes.get(0).context("")?, true);
        query_dag.add_edge(diff_idx, *sub_root_idxes.get(1).context("")?, false);
    }
    let res_query = Query {
        end_blk_height,
        query_dag,
        trie_proofs: HashMap::<Height, trie_tree::proof::Proof>::new(),
    };

    Ok(res_query)
}

pub fn param_to_query_trimmed2<K: Num, T: ReadInterface<K = K>>(
    time_win: TimeWin,
    query_content: &QueryContent<K>,
    chain: &T,
    pk: &AccPublicKey,
    start_win_size: Option<u64>,
    end_win_size: u64,
) -> Result<Query<K>> {
    let start_blk_height = Height(time_win.start_blk);
    let end_blk_height = Height(time_win.end_blk);
    let keyword_exp_opt = query_content.keyword_exp.as_ref();
    let mut query_dag = Graph::<QueryNode<K>, bool>::new();
    let mut heights = vec![(end_win_size, end_blk_height)];
    if let Some(win_size) = start_win_size {
        if start_blk_height.0 > 1 {
            heights.push((win_size, Height(start_blk_height.0 - 1)));
        }
    }
    debug!("heights: {:?}", heights);

    let has_range_query: bool;
    if query_content.range.is_empty() {
        has_range_query = false;
    } else {
        has_range_query = true;
    }

    let mut sub_root_idxes = Vec::<NodeIndex>::new();
    let mut trie_proofs = HashMap::<Height, trie_tree::proof::Proof>::new();
    let mut end_blk_res_size = 0;
    for (win_size, height) in heights {
        let mut sub_root_idx: NodeIndex = NodeIndex::default(); // attention, here should not be 0
        let trie_root = chain
            .read_block_content(height)?
            .ads
            .read_trie_root(win_size)?;
        let mut trie_ctx = trie_tree::read::ReadContext::new(chain, trie_root.trie_root_id);

        let mut sub_graphs = Vec::<(usize, NodeIndex, Graph<QueryNode<K>, bool>)>::new();
        if let Some(keyword_exp) = keyword_exp_opt.as_ref() {
            let k_exp_set = keyword_exp.to_cnf_set();
            for k_exp in &k_exp_set {
                let (cost, sub_rt_idx, sub_graph) =
                    process_sub_node(k_exp, height, win_size, &mut trie_ctx, chain, pk)?;
                sub_graphs.push((cost, sub_rt_idx, sub_graph));
            }
            trie_proofs.insert(height, trie_ctx.into_proof());
        }

        if has_range_query {
            for (i, r) in query_content.range.iter().enumerate() {
                let mut range_node = RangeNode {
                    range: *r,
                    blk_height: height,
                    time_win: win_size,
                    dim: i,
                    set: None,
                };
                range_node.estimate_size(chain, pk)?;
                let mut sub_graph = Graph::<QueryNode<K>, bool>::new();
                let rt_idx = sub_graph.add_node(QueryNode::Range(range_node));
                sub_graphs.push((0, rt_idx, sub_graph));
            }
        }
        sub_graphs.sort_by(|a, b| a.0.cmp(&b.0));
        if height == end_blk_height {
            let mut lock = false;
            for (_, sub_rt_idx, sub_graph) in &mut sub_graphs {
                if lock {
                    sub_root_idx = combine_query_graphs_by_intersec(
                        &mut query_dag,
                        sub_root_idx,
                        sub_graph,
                        *sub_rt_idx,
                    )?;
                    continue;
                }
                sub_root_idx = combine_query_graphs(&mut query_dag, sub_graph, *sub_rt_idx)?;
                lock = true;
            }
            end_blk_res_size = query_dag
                .node_weight(sub_root_idx)
                .context("Caonnt find root of end blk dag")?
                .get_set()?
                .len();
        } else {
            let cur_cost = std::usize::MAX;
            let mut lock = false;
            for (sub_cost, sub_rt_idx, sub_graph) in &mut sub_graphs {
                let sub_res_size = sub_graph
                    .node_weight(*sub_rt_idx)
                    .context("")?
                    .get_set()?
                    .len();
                let cost = *sub_cost + sub_res_size * end_blk_res_size;
                if cur_cost > cost {
                    if lock {
                        sub_root_idx = combine_query_graphs_by_intersec(
                            &mut query_dag,
                            sub_root_idx,
                            sub_graph,
                            *sub_rt_idx,
                        )?;
                        continue;
                    }
                    sub_root_idx = combine_query_graphs(&mut query_dag, sub_graph, *sub_rt_idx)?;
                    lock = true;
                } else {
                    break;
                }
            }
        }
        sub_root_idxes.push(sub_root_idx);
    }
    if sub_root_idxes.len() > 1 {
        let diff_idx = query_dag.add_node(QueryNode::Diff(DiffNode { set: None }));
        query_dag.add_edge(diff_idx, *sub_root_idxes.get(1).context("")?, true);
        query_dag.add_edge(diff_idx, *sub_root_idxes.get(0).context("")?, false);
    }

    let res_query = Query {
        end_blk_height,
        query_dag,
        trie_proofs,
    };

    Ok(res_query)
}

fn dag_add_keyword_exp<K: Num>(
    keyword_exp: &Node,
    dag: &mut Graph<QueryNode<K>, bool>,
    blk_height: Height,
    win_size: u64,
) -> Result<NodeIndex> {
    let mut queue = VecDeque::<(&Node, NodeIndex)>::new();
    let mut idx_map = HashMap::<String, NodeIndex>::new();
    let keyword_root_idx: NodeIndex;
    match keyword_exp {
        Node::And(n) => {
            let idx = dag.add_node(QueryNode::Intersec(IntersecNode { set: None }));
            keyword_root_idx = idx;
            let AndNode(c1, c2) = n.as_ref();
            let idx1: NodeIndex;
            let idx2: NodeIndex;
            match c1 {
                Node::And(_) => {
                    idx1 = dag.add_node(QueryNode::Intersec(IntersecNode { set: None }));
                }
                Node::Or(_) => {
                    idx1 = dag.add_node(QueryNode::Union(UnionNode { set: None }));
                }
                Node::Not(_) => {
                    idx1 = dag.add_node(QueryNode::Diff(DiffNode { set: None }));
                }
                Node::Input(s) => {
                    idx1 = dag.add_node(QueryNode::Keyword(Box::new(KeywordNode {
                        keyword: s.to_string(),
                        blk_height,
                        time_win: win_size,
                        set: None,
                    })));
                    idx_map.insert(s.to_string(), idx1);
                }
            }
            dag.add_edge(idx, idx1, true);
            match c2 {
                Node::And(_) => {
                    idx2 = dag.add_node(QueryNode::Intersec(IntersecNode { set: None }));
                }
                Node::Or(_) => {
                    idx2 = dag.add_node(QueryNode::Union(UnionNode { set: None }));
                }
                Node::Not(_) => {
                    idx2 = dag.add_node(QueryNode::Diff(DiffNode { set: None }));
                }
                Node::Input(s) => {
                    idx2 = dag.add_node(QueryNode::Keyword(Box::new(KeywordNode {
                        keyword: s.to_string(),
                        blk_height,
                        time_win: win_size,
                        set: None,
                    })));
                    idx_map.insert(s.to_string(), idx2);
                }
            }
            dag.add_edge(idx, idx2, false);
            queue.push_back((c1, idx1));
            queue.push_back((c2, idx2));
        }
        Node::Or(n) => {
            let idx = dag.add_node(QueryNode::Union(UnionNode { set: None }));
            keyword_root_idx = idx;
            let OrNode(c1, c2) = n.as_ref();
            let idx1: NodeIndex;
            let idx2: NodeIndex;
            match c1 {
                Node::And(_) => {
                    idx1 = dag.add_node(QueryNode::Intersec(IntersecNode { set: None }));
                }
                Node::Or(_) => {
                    idx1 = dag.add_node(QueryNode::Union(UnionNode { set: None }));
                }
                Node::Not(_) => {
                    idx1 = dag.add_node(QueryNode::Diff(DiffNode { set: None }));
                }
                Node::Input(s) => {
                    idx1 = dag.add_node(QueryNode::Keyword(Box::new(KeywordNode {
                        keyword: s.to_string(),
                        blk_height,
                        time_win: win_size,
                        set: None,
                    })));
                    idx_map.insert(s.to_string(), idx1);
                }
            }
            dag.add_edge(idx, idx1, true);
            match c2 {
                Node::And(_) => {
                    idx2 = dag.add_node(QueryNode::Intersec(IntersecNode { set: None }));
                }
                Node::Or(_) => {
                    idx2 = dag.add_node(QueryNode::Union(UnionNode { set: None }));
                }
                Node::Not(_) => {
                    idx2 = dag.add_node(QueryNode::Diff(DiffNode { set: None }));
                }
                Node::Input(s) => {
                    idx2 = dag.add_node(QueryNode::Keyword(Box::new(KeywordNode {
                        keyword: s.to_string(),
                        blk_height,
                        time_win: win_size,
                        set: None,
                    })));
                    idx_map.insert(s.to_string(), idx2);
                }
            }
            dag.add_edge(idx, idx2, false);
            queue.push_back((c1, idx1));
            queue.push_back((c2, idx2));
        }
        Node::Not(n) => {
            let idx = dag.add_node(QueryNode::Diff(DiffNode { set: None }));
            keyword_root_idx = idx;
            let NotNode(c) = n.as_ref();
            let c_idx: NodeIndex;
            match c {
                Node::And(_) => {
                    c_idx = dag.add_node(QueryNode::Intersec(IntersecNode { set: None }));
                }
                Node::Or(_) => {
                    c_idx = dag.add_node(QueryNode::Union(UnionNode { set: None }));
                }
                Node::Not(_) => {
                    c_idx = dag.add_node(QueryNode::Diff(DiffNode { set: None }));
                }
                Node::Input(s) => {
                    c_idx = dag.add_node(QueryNode::Keyword(Box::new(KeywordNode {
                        keyword: s.to_string(),
                        blk_height,
                        time_win: win_size,
                        set: None,
                    })));
                    idx_map.insert(s.to_string(), c_idx);
                }
            }
            dag.add_edge(idx, c_idx, true);
            let blk_rt_idx = dag.add_node(QueryNode::BlkRt(Box::new(BlkRtNode {
                blk_height,
                time_win: win_size,
                set: None,
            })));
            dag.add_edge(idx, blk_rt_idx, false);
            queue.push_back((c, c_idx));
        }
        Node::Input(s) => {
            let idx = dag.add_node(QueryNode::Keyword(Box::new(KeywordNode {
                keyword: s.to_string(),
                blk_height,
                time_win: win_size,
                set: None,
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
                        idx1 = dag.add_node(QueryNode::Intersec(IntersecNode { set: None }));
                    }
                    Node::Or(_) => {
                        idx1 = dag.add_node(QueryNode::Union(UnionNode { set: None }));
                    }
                    Node::Not(_) => {
                        idx1 = dag.add_node(QueryNode::Diff(DiffNode { set: None }));
                    }
                    Node::Input(s) => {
                        if let Some(c_idx) = idx_map.get(s) {
                            idx1 = *c_idx;
                        } else {
                            idx1 = dag.add_node(QueryNode::Keyword(Box::new(KeywordNode {
                                keyword: s.to_string(),
                                blk_height,
                                time_win: win_size,
                                set: None,
                            })));
                            idx_map.insert(s.to_string(), idx1);
                        }
                    }
                }
                dag.add_edge(idx, idx1, true);
                match c2 {
                    Node::And(_) => {
                        idx2 = dag.add_node(QueryNode::Intersec(IntersecNode { set: None }));
                    }
                    Node::Or(_) => {
                        idx2 = dag.add_node(QueryNode::Union(UnionNode { set: None }));
                    }
                    Node::Not(_) => {
                        idx2 = dag.add_node(QueryNode::Diff(DiffNode { set: None }));
                    }
                    Node::Input(s) => {
                        if let Some(c_idx) = idx_map.get(s) {
                            idx2 = *c_idx;
                        } else {
                            idx2 = dag.add_node(QueryNode::Keyword(Box::new(KeywordNode {
                                keyword: s.to_string(),
                                blk_height,
                                time_win: win_size,
                                set: None,
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
                        idx1 = dag.add_node(QueryNode::Intersec(IntersecNode { set: None }));
                    }
                    Node::Or(_) => {
                        idx1 = dag.add_node(QueryNode::Union(UnionNode { set: None }));
                    }
                    Node::Not(_) => {
                        idx1 = dag.add_node(QueryNode::Diff(DiffNode { set: None }));
                    }
                    Node::Input(s) => {
                        if let Some(c_idx) = idx_map.get(s) {
                            idx1 = *c_idx;
                        } else {
                            idx1 = dag.add_node(QueryNode::Keyword(Box::new(KeywordNode {
                                keyword: s.to_string(),
                                blk_height,
                                time_win: win_size,
                                set: None,
                            })));
                            idx_map.insert(s.to_string(), idx1);
                        }
                    }
                }
                dag.add_edge(idx, idx1, true);
                match c2 {
                    Node::And(_) => {
                        idx2 = dag.add_node(QueryNode::Intersec(IntersecNode { set: None }));
                    }
                    Node::Or(_) => {
                        idx2 = dag.add_node(QueryNode::Union(UnionNode { set: None }));
                    }
                    Node::Not(_) => {
                        idx2 = dag.add_node(QueryNode::Diff(DiffNode { set: None }));
                    }
                    Node::Input(s) => {
                        if let Some(c_idx) = idx_map.get(s) {
                            idx2 = *c_idx;
                        } else {
                            idx2 = dag.add_node(QueryNode::Keyword(Box::new(KeywordNode {
                                keyword: s.to_string(),
                                blk_height,
                                time_win: win_size,
                                set: None,
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
                let blk_rt_idx = dag.add_node(QueryNode::BlkRt(Box::new(BlkRtNode {
                    blk_height,
                    time_win: win_size,
                    set: None,
                })));
                match c {
                    Node::And(_) => {
                        c_idx = dag.add_node(QueryNode::Intersec(IntersecNode { set: None }));
                    }
                    Node::Or(_) => {
                        c_idx = dag.add_node(QueryNode::Union(UnionNode { set: None }));
                    }
                    Node::Not(_) => {
                        c_idx = dag.add_node(QueryNode::Diff(DiffNode { set: None }));
                    }
                    Node::Input(s) => {
                        if let Some(ch_idx) = idx_map.get(s) {
                            c_idx = *ch_idx;
                        } else {
                            c_idx = dag.add_node(QueryNode::Keyword(Box::new(KeywordNode {
                                keyword: s.to_string(),
                                blk_height,
                                time_win: win_size,
                                set: None,
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

fn process_sub_node<K: Num, T: ReadInterface<K = K>>(
    sub_exp: &Node,
    blk_height: Height,
    win_size: u64,
    trie_ctx: &mut trie_tree::read::ReadContext<T>,
    chain: &T,
    pk: &AccPublicKey,
) -> Result<(usize, NodeIndex, Graph<QueryNode<K>, bool>)> {
    let mut sub_dag = Graph::<QueryNode<K>, bool>::new();
    let sub_root_idx = dag_add_keyword_exp(sub_exp, &mut sub_dag, blk_height, win_size)?;
    let mut inputs = match toposort(&sub_dag, None) {
        Ok(v) => v,
        Err(_) => {
            bail!("Input query plan graph not valid")
        }
    };
    inputs.reverse();

    let cost = estimate_query_cost(&inputs, &mut sub_dag, trie_ctx, chain, pk)?;

    Ok((cost, sub_root_idx, sub_dag))
}

fn combine_query_graphs_by_intersec<K: Num>(
    graph1: &mut Graph<QueryNode<K>, bool>,
    graph1_root_idx: NodeIndex,
    graph2: &mut Graph<QueryNode<K>, bool>,
    graph2_root_idx: NodeIndex,
) -> Result<NodeIndex> {
    let new_graph2_sub_root_idx = combine_query_graphs(graph1, graph2, graph2_root_idx)?;
    let s1 = graph1
        .node_weight(graph1_root_idx)
        .context("Cannot find subroot1")?
        .get_set()?;
    let s2 = graph1
        .node_weight(new_graph2_sub_root_idx)
        .context("Cannot find subroot1")?
        .get_set()?;
    let s_new = s1 & s2;
    let new_root_idx = graph1.add_node(QueryNode::Intersec(IntersecNode { set: Some(s_new) }));
    graph1.add_edge(new_root_idx, graph1_root_idx, true);
    graph1.add_edge(new_root_idx, new_graph2_sub_root_idx, false);
    Ok(new_root_idx)
}

fn combine_query_graphs<K: Num>(
    graph1: &mut Graph<QueryNode<K>, bool>,
    graph2: &mut Graph<QueryNode<K>, bool>,
    graph2_root_idx: NodeIndex,
) -> Result<NodeIndex> {
    let mut old_new_idx = HashMap::<NodeIndex, NodeIndex>::new();
    let mut old_s_e_idx = Vec::<(NodeIndex, NodeIndex, bool)>::new();

    let graph2_idxes = graph2.node_indices();
    for idx in graph2_idxes.rev() {
        for c_idx in graph2.neighbors_directed(idx, Outgoing) {
            let edge_idx = graph2.find_edge(idx, c_idx).context("Cannot find edge")?;
            let weight = graph2.edge_weight(edge_idx).context("Cannot find edge")?;
            old_s_e_idx.push((idx, c_idx, *weight));
        }
        for p_idx in graph2.neighbors_directed(idx, Incoming) {
            let edge_idx = graph2.find_edge(p_idx, idx).context("Cannot find edge")?;
            let weight = graph2.edge_weight(edge_idx).context("Cannot find edge")?;
            old_s_e_idx.push((p_idx, idx, *weight));
        }
        let node = graph2.remove_node(idx).context("Node does not exist")?;
        let new_idx = graph1.add_node(node);
        old_new_idx.insert(idx, new_idx);
    }

    for (old_s, old_e, weight) in old_s_e_idx.iter().rev() {
        let new_s = old_new_idx.get(old_s).context("Cannot find idx in map")?;
        let new_e = old_new_idx.get(old_e).context("Cannot find idx in map")?;
        graph1.add_edge(*new_s, *new_e, *weight);
    }

    let sub_root = old_new_idx
        .get(&graph2_root_idx)
        .context("Cannot find graph2 root index")?;
    Ok(*sub_root)
}

fn get_range_idxs_sorted(mut vec: Vec<(usize, NodeIndex, Set)>) -> Vec<NodeIndex> {
    let (vec_unsorted, cost_unsorted) = get_intersec_cost(&vec);
    vec.sort_by(|a, b| a.0.cmp(&b.0));
    let (vec_sorted, cost_sorted) = get_intersec_cost(&vec);
    if cost_unsorted < cost_sorted {
        vec_unsorted
    } else {
        vec_sorted
    }
}

fn get_intersec_cost(vec: &[(usize, NodeIndex, Set)]) -> (Vec<NodeIndex>, usize) {
    let mut res = Vec::<NodeIndex>::new();
    let mut res_cost: usize = 0;
    let mut range_lock = false;
    let mut cur_set;
    let mut cur_set_ref = &Set::new();
    for (_size, idx, set) in vec {
        res.push(*idx);
        if range_lock {
            res_cost += cur_set_ref.len() * set.len();
            cur_set = (cur_set_ref) & (set);
            cur_set_ref = &cur_set;
            continue;
        }
        cur_set_ref = set;
        range_lock = true;
    }
    (res, res_cost)
}

#[cfg(test)]
mod tests {
    use crate::chain::{
        query::{
            query_param::{param_to_query_basic, AndNode, Node, NotNode, OrNode, QueryParam},
            select_win_size,
        },
        range::Range,
    };
    use petgraph::dot::{Config, Dot};

    use serde_json::json;

    #[test]
    fn test_query_param() {
        let data = json!({
            "start_blk": 1,
            "end_blk": 3,
            "range": [],
            "keyword_exp": {
                "or": [
                    {"input": "a"},
                    {"not": {"input": "b"}},
                ]
            },
        });
        let query_param: QueryParam<u32> = serde_json::from_value(data).unwrap();
        let expect = QueryParam::<u32> {
            start_blk: 1,
            end_blk: 3,
            range: vec![],
            keyword_exp: Some(Node::Or(Box::new(OrNode(
                Node::Input("a".to_string()),
                Node::Not(Box::new(NotNode(Node::Input("b".to_string())))),
            )))),
        };
        assert_eq!(query_param, expect);

        let data = json!({
            "start_blk": 1,
            "end_blk": 3,
            "range": [(1, 5), (2, 8)],
            "keyword_exp": {
                "or": [
                    {"input": "a"},
                    {"not": {"input": "b"}},
                ]
            },
        });
        let query_param: QueryParam<u32> = serde_json::from_value(data).unwrap();
        let expect = QueryParam::<u32> {
            start_blk: 1,
            end_blk: 3,
            range: vec![Range::<u32>::new(1, 5), Range::<u32>::new(2, 8)],
            keyword_exp: Some(Node::Or(Box::new(OrNode(
                Node::Input("a".to_string()),
                Node::Not(Box::new(NotNode(Node::Input("b".to_string())))),
            )))),
        };
        assert_eq!(query_param, expect);

        let data = json!({
            "start_blk": 1,
            "end_blk": 3,
            "range": [(1, 5), (2, 8)],
            "keyword_exp": null,
        });
        let query_param: QueryParam<u32> = serde_json::from_value(data).unwrap();
        let expect = QueryParam::<u32> {
            start_blk: 1,
            end_blk: 3,
            range: vec![Range::<u32>::new(1, 5), Range::<u32>::new(2, 8)],
            keyword_exp: None,
        };
        assert_eq!(query_param, expect);
    }

    #[test]
    fn test_to_query() {
        let data = json!({
            "start_blk": 2,
            "end_blk": 4,
            "range": [(1, 5), (2, 8)],
            "keyword_exp": {
                "or": [
                    {"input": "a"},
                    {"and": [{"input": "b"}, {"input": "c"}]},
                ]
            },
        });
        let query_param: QueryParam<u32> = serde_json::from_value(data).unwrap();
        let query_time_win = query_param.gen_time_win();
        let query_content = query_param.gen_query_content();
        let time_wins: Vec<u64> = vec![4];
        let query_params = select_win_size(&time_wins, query_time_win).unwrap();
        for (time_win, s_win_size, e_win_size) in query_params {
            let query =
                param_to_query_basic(time_win, &query_content, s_win_size, e_win_size).unwrap();
            let query_dag = query.query_dag;
            println!("{:?}", Dot::with_config(&query_dag, &[Config::EdgeNoLabel]));
        }
        println!("======================");
        let data = json!({
            "start_blk": 2,
            "end_blk": 8,
            "range": [(1, 5)],
            "keyword_exp": {"input": "a"},
        });
        let query_param: QueryParam<u32> = serde_json::from_value(data).unwrap();
        let query_time_win = query_param.gen_time_win();
        let query_content = query_param.gen_query_content();
        let time_wins: Vec<u64> = vec![4];
        let query_params = select_win_size(&time_wins, query_time_win).unwrap();
        for (time_win, s_win_size, e_win_size) in query_params {
            let query =
                param_to_query_basic(time_win, &query_content, s_win_size, e_win_size).unwrap();
            let query_dag = query.query_dag;
            println!("{:?}", Dot::with_config(&query_dag, &[Config::EdgeNoLabel]));
        }
        println!("======================");
        let data = json!({
            "start_blk": 1,
            "end_blk": 3,
            "range": [(10, 15)],
            "keyword_exp": {"input": "a"},
        });
        let query_param: QueryParam<u32> = serde_json::from_value(data).unwrap();
        let query_time_win = query_param.gen_time_win();
        let query_content = query_param.gen_query_content();
        let time_wins: Vec<u64> = vec![4];
        let query_params = select_win_size(&time_wins, query_time_win).unwrap();
        for (time_win, s_win_size, e_win_size) in query_params {
            let query =
                param_to_query_basic(time_win, &query_content, s_win_size, e_win_size).unwrap();
            let query_dag = query.query_dag;
            println!("{:?}", Dot::with_config(&query_dag, &[Config::EdgeNoLabel]));
        }
        println!("======================");
        let data = json!({
            "start_blk": 2,
            "end_blk": 4,
            "range": [(10, 15)],
            "keyword_exp": {
                "not": {"input": "a"}
            },
        });
        let query_param: QueryParam<u32> = serde_json::from_value(data).unwrap();
        let query_time_win = query_param.gen_time_win();
        let query_content = query_param.gen_query_content();
        let time_wins: Vec<u64> = vec![4];
        let query_params = select_win_size(&time_wins, query_time_win).unwrap();
        for (time_win, s_win_size, e_win_size) in query_params {
            let query =
                param_to_query_basic(time_win, &query_content, s_win_size, e_win_size).unwrap();
            let query_dag = query.query_dag;
            println!("{:?}", Dot::with_config(&query_dag, &[Config::EdgeNoLabel]));
        }

        assert_eq!(1, 1);
    }

    #[test]
    fn test_to_cnf() {
        let exp = Node::Input("a".to_string());
        let exp_cnf = exp.to_cnf_set();
        println!("CNF: {:?}", exp_cnf);
        println!("====================");
        let exp = Node::And(Box::new(AndNode(
            Node::Input("a".to_string()),
            Node::Input("b".to_string()),
        )));
        let exp_cnf = exp.to_cnf_set();
        println!("CNF: {:?}", exp_cnf);
        println!("====================");
        let exp = Node::Or(Box::new(OrNode(
            Node::Input("a".to_string()),
            Node::Input("b".to_string()),
        )));
        let exp_cnf = exp.to_cnf_set();
        println!("CNF: {:?}", exp_cnf);
        println!("====================");
        let exp = Node::And(Box::new(AndNode(
            Node::Or(Box::new(OrNode(
                Node::Input("a".to_string()),
                Node::Input("b".to_string()),
            ))),
            Node::Input("c".to_string()),
        )));
        let exp_cnf = exp.to_cnf_set();
        println!("CNF: {:?}", exp_cnf);
        println!("====================");
        let exp = Node::Or(Box::new(OrNode(
            Node::And(Box::new(AndNode(
                Node::Input("a".to_string()),
                Node::Input("b".to_string()),
            ))),
            Node::Input("c".to_string()),
        )));
        let exp_cnf = exp.to_cnf_set();
        println!("CNF: {:?}", exp_cnf);
        println!("====================");
        let exp = Node::Or(Box::new(OrNode(
            Node::And(Box::new(AndNode(
                Node::Input("a".to_string()),
                Node::Input("b".to_string()),
            ))),
            Node::And(Box::new(AndNode(
                Node::Input("c".to_string()),
                Node::Input("d".to_string()),
            ))),
        )));
        let exp_cnf = exp.to_cnf_set();
        println!("CNF: {:?}", exp_cnf);
        println!("====================");
        let exp = Node::And(Box::new(AndNode(
            Node::Or(Box::new(OrNode(
                Node::Input("a".to_string()),
                Node::Input("b".to_string()),
            ))),
            Node::Or(Box::new(OrNode(
                Node::Input("c".to_string()),
                Node::Input("d".to_string()),
            ))),
        )));
        let exp_cnf = exp.to_cnf_set();
        println!("CNF: {:?}", exp_cnf);

        assert_eq!(1, 1);
    }
}
