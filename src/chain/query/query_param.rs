use super::{query_dag::DagNode, query_plan::QueryPlan, QueryContent, TimeWin};
use crate::{
    acc::AccPublicKey,
    chain::{
        block::Height,
        bplus_tree,
        query::query_plan::{
            QPBlkRtNode, QPDiff, QPIntersec, QPKeywordNode, QPNode, QPRangeNode, QPUnion,
        },
        range::Range,
        traits::{Num, ReadInterface},
        trie_tree,
    },
};
use anyhow::{bail, Context, Result};
use petgraph::{algo::toposort, graph::NodeIndex, EdgeDirection::Outgoing, Graph};
use serde::{Deserialize, Serialize};
use smol_str::SmolStr;
use std::collections::{HashMap, HashSet};

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
    pub start_blk: u32,
    pub end_blk: u32,
    pub range: Vec<Range<K>>,
    pub keyword_exp: Option<Node>,
}

impl<K: Num> QueryParam<K> {
    pub fn get_start(&self) -> u32 {
        self.start_blk
    }

    pub fn get_end(&self) -> u32 {
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

pub fn param_to_qp<K: Num, T: ReadInterface<K = K>>(
    time_win: &TimeWin,
    e_win_size: u16,
    query_dag: &Graph<DagNode<K>, bool>,
    chain: &T,
    pk: &AccPublicKey,
) -> Result<QueryPlan<K>> {
    let end_blk_height = Height(time_win.get_end());
    let mut dag_content = HashMap::<NodeIndex, QPNode<K>>::new();
    let mut q_inputs = match toposort(&query_dag, None) {
        Ok(v) => v,
        Err(_) => {
            bail!("Input query graph not valid")
        }
    };
    q_inputs.reverse();
    let mut trie_ctxes = HashMap::<Height, trie_tree::read::ReadContext<T>>::new();

    for idx in &q_inputs {
        if let Some(node) = query_dag.node_weight(*idx) {
            match node {
                DagNode::Range(n) => {
                    let bplus_root = chain
                        .read_block_content(end_blk_height)?
                        .ads
                        .read_bplus_root(e_win_size, n.dim)?;
                    let (s, a, p) = bplus_tree::read::range_query(
                        chain,
                        bplus_root.bplus_tree_root_id,
                        n.range,
                        pk,
                    )?;
                    let qp_range_node: QPRangeNode<K> = QPRangeNode {
                        blk_height: end_blk_height,
                        set: Some((s, a, p)),
                    };
                    dag_content.insert(*idx, QPNode::Range(Box::new(qp_range_node)));
                }
                DagNode::Keyword(n) => {
                    let set;
                    let acc;
                    if let Some(ctx) = trie_ctxes.get_mut(&end_blk_height) {
                        let (s, a) = ctx.query(&SmolStr::from(&n.keyword), pk)?;
                        set = s;
                        acc = a;
                    } else {
                        let trie_root = chain
                            .read_block_content(end_blk_height)?
                            .ads
                            .read_trie_root(e_win_size)?;
                        let mut trie_ctx =
                            trie_tree::read::ReadContext::new(chain, trie_root.trie_root_id);
                        let (s, a) = trie_ctx.query(&SmolStr::from(&n.keyword), pk)?;
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
                    let blk_content = chain.read_block_content(end_blk_height)?;
                    let bplus_root = blk_content.ads.read_bplus_root(e_win_size, 0)?;
                    let bplus_root_id =
                        bplus_root.bplus_tree_root_id.context("Empty bplus root")?;
                    let bplus_root_node =
                        bplus_tree::BPlusTreeNodeLoader::load_node(chain, bplus_root_id)?;
                    let set = bplus_root_node.get_set().clone();
                    let acc = bplus_root_node.get_node_acc();
                    let qp_blk_rt_node = QPBlkRtNode {
                        blk_height: end_blk_height,
                        set: Some((set, acc)),
                    };
                    dag_content.insert(*idx, QPNode::BlkRt(Box::new(qp_blk_rt_node)));
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
                    let qp_union = QPUnion { set: Some(c_union) };
                    dag_content.insert(*idx, QPNode::Union(qp_union));
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
                    let qp_intersec = QPIntersec {
                        set: Some(c_intersec),
                    };
                    dag_content.insert(*idx, QPNode::Intersec(qp_intersec));
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
                    let qp_diff = QPDiff { set: Some(c_diff) };
                    dag_content.insert(*idx, QPNode::Diff(qp_diff));
                }
            }
        }
    }

    let q_output_elm = q_inputs
        .last()
        .cloned()
        .context("Input query graph is empty")?;
    let qp_root_idx = q_output_elm;

    let mut trie_proofs = HashMap::<Height, trie_tree::proof::Proof>::new();
    for (height, trie_ctx) in trie_ctxes {
        trie_proofs.insert(height, trie_ctx.into_proof());
    }
    Ok(QueryPlan {
        end_blk_height,
        root_idx: qp_root_idx,
        dag_content,
        trie_proofs,
    })
}

#[cfg(test)]
mod tests {
    use crate::chain::{
        query::query_param::{AndNode, Node, NotNode, OrNode, QueryParam},
        range::Range,
    };
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
