use crate::{
    chain::{
        block::Height,
        query::query_obj::{
            BlkRtNode, DiffNode, IntersecNode, KeywordNode, Query, QueryNode, RangeNode, UnionNode,
        },
        range::Range,
        traits::Num,
    },
    digest::Digest,
};
use anyhow::{bail, Result};
use petgraph::{graph::NodeIndex, Graph};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub(crate) enum Node {
    And(Box<AndNode>),
    Or(Box<OrNode>),
    Not(Box<NotNode>),
    Input(String),
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub(crate) struct AndNode(Node, Node);

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub(crate) struct OrNode(Node, Node);

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub(crate) struct NotNode(Node);

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct QueryParam<K: Num> {
    pub(crate) start_blk: u64,
    pub(crate) end_blk: u64,
    pub(crate) range: Vec<Range<K>>,
    pub(crate) keyword_exp: Option<Node>,
}

impl<K: Num> QueryParam<K> {
    pub fn get_start(&self) -> u64 {
        self.start_blk
    }

    pub fn get_end(&self) -> u64 {
        self.end_blk
    }

    pub fn copy_on_write(&self, new_start_blk: u64, new_end_blk: u64) -> Self {
        Self {
            start_blk: new_start_blk,
            end_blk: new_end_blk,
            range: self.range.clone(),
            keyword_exp: self.keyword_exp.clone(),
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn into_query_basic(
        self,
        start_win_size: Option<u64>,
        end_win_size: u64,
    ) -> Result<(Query<K>, HashMap<NodeIndex, HashSet<Digest>>)> {
        let end_blk_height = Height(self.end_blk);
        let keyword_exp_opt = self.keyword_exp;
        let mut query_dag = Graph::<QueryNode<K>, ()>::new();
        let mut queue = VecDeque::<(Node, NodeIndex)>::new();
        let mut idx_map = HashMap::<String, NodeIndex>::new();

        let mut keyword_root_idx: NodeIndex = NodeIndex::default();
        let mut range_root_idx: NodeIndex = NodeIndex::default();
        let has_keyword_query: bool;
        let has_range_query: bool;

        if let Some(keyword_exp) = keyword_exp_opt {
            has_keyword_query = true;

            match keyword_exp {
                Node::And(n) => {
                    let idx = query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
                    keyword_root_idx = idx;
                    let AndNode(c1, c2) = *n;
                    let idx1: NodeIndex;
                    let idx2: NodeIndex;
                    match &c1 {
                        Node::And(_) => {
                            idx1 = query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
                        }
                        Node::Or(_) => {
                            idx1 = query_dag.add_node(QueryNode::Union(UnionNode {}));
                        }
                        Node::Not(_) => {
                            idx1 = query_dag.add_node(QueryNode::Diff(DiffNode {}));
                        }
                        Node::Input(s) => {
                            idx1 = query_dag.add_node(QueryNode::Keyword(KeywordNode {
                                keyword: s.to_string(),
                                blk_height: end_blk_height,
                                time_win: end_win_size,
                            }));
                            idx_map.insert(s.to_string(), idx1);
                        }
                    }
                    query_dag.add_edge(idx, idx1, ());
                    match &c2 {
                        Node::And(_) => {
                            idx2 = query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
                        }
                        Node::Or(_) => {
                            idx2 = query_dag.add_node(QueryNode::Union(UnionNode {}));
                        }
                        Node::Not(_) => {
                            idx2 = query_dag.add_node(QueryNode::Diff(DiffNode {}));
                        }
                        Node::Input(s) => {
                            idx2 = query_dag.add_node(QueryNode::Keyword(KeywordNode {
                                keyword: s.to_string(),
                                blk_height: end_blk_height,
                                time_win: end_win_size,
                            }));
                            idx_map.insert(s.to_string(), idx2);
                        }
                    }
                    query_dag.add_edge(idx, idx2, ());
                    queue.push_back((c1, idx1));
                    queue.push_back((c2, idx2));
                }
                Node::Or(n) => {
                    let idx = query_dag.add_node(QueryNode::Union(UnionNode {}));
                    keyword_root_idx = idx;
                    let OrNode(c1, c2) = *n;
                    let idx1: NodeIndex;
                    let idx2: NodeIndex;
                    match &c1 {
                        Node::And(_) => {
                            idx1 = query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
                        }
                        Node::Or(_) => {
                            idx1 = query_dag.add_node(QueryNode::Union(UnionNode {}));
                        }
                        Node::Not(_) => {
                            idx1 = query_dag.add_node(QueryNode::Diff(DiffNode {}));
                        }
                        Node::Input(s) => {
                            idx1 = query_dag.add_node(QueryNode::Keyword(KeywordNode {
                                keyword: s.to_string(),
                                blk_height: end_blk_height,
                                time_win: end_win_size,
                            }));
                            idx_map.insert(s.to_string(), idx1);
                        }
                    }
                    query_dag.add_edge(idx, idx1, ());
                    match &c2 {
                        Node::And(_) => {
                            idx2 = query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
                        }
                        Node::Or(_) => {
                            idx2 = query_dag.add_node(QueryNode::Union(UnionNode {}));
                        }
                        Node::Not(_) => {
                            idx2 = query_dag.add_node(QueryNode::Diff(DiffNode {}));
                        }
                        Node::Input(s) => {
                            idx2 = query_dag.add_node(QueryNode::Keyword(KeywordNode {
                                keyword: s.to_string(),
                                blk_height: end_blk_height,
                                time_win: end_win_size,
                            }));
                            idx_map.insert(s.to_string(), idx2);
                        }
                    }
                    query_dag.add_edge(idx, idx2, ());
                    queue.push_back((c1, idx1));
                    queue.push_back((c2, idx2));
                }
                Node::Not(n) => {
                    let idx = query_dag.add_node(QueryNode::Diff(DiffNode {}));
                    keyword_root_idx = idx;
                    let NotNode(c) = *n;
                    let c_idx: NodeIndex;
                    match &c {
                        Node::And(_) => {
                            c_idx = query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
                        }
                        Node::Or(_) => {
                            c_idx = query_dag.add_node(QueryNode::Union(UnionNode {}));
                        }
                        Node::Not(_) => {
                            c_idx = query_dag.add_node(QueryNode::Diff(DiffNode {}));
                        }
                        Node::Input(s) => {
                            c_idx = query_dag.add_node(QueryNode::Keyword(KeywordNode {
                                keyword: s.to_string(),
                                blk_height: end_blk_height,
                                time_win: end_win_size,
                            }));
                            idx_map.insert(s.to_string(), c_idx);
                        }
                    }
                    query_dag.add_edge(idx, c_idx, ());
                    let blk_rt_idx = query_dag.add_node(QueryNode::BlkRt(BlkRtNode {
                        blk_height: end_blk_height,
                        time_win: end_win_size,
                    }));
                    query_dag.add_edge(idx, blk_rt_idx, ());
                    queue.push_back((c, c_idx));
                }
                Node::Input(s) => {
                    let idx = query_dag.add_node(QueryNode::Keyword(KeywordNode {
                        keyword: s,
                        blk_height: end_blk_height,
                        time_win: end_win_size,
                    }));
                    keyword_root_idx = idx;
                }
            }

            while let Some(node) = queue.pop_front() {
                match node {
                    (Node::And(n), idx) => {
                        let AndNode(c1, c2) = *n;
                        let idx1: NodeIndex;
                        let idx2: NodeIndex;
                        match &c1 {
                            Node::And(_) => {
                                idx1 = query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
                            }
                            Node::Or(_) => {
                                idx1 = query_dag.add_node(QueryNode::Union(UnionNode {}));
                            }
                            Node::Not(_) => {
                                idx1 = query_dag.add_node(QueryNode::Diff(DiffNode {}));
                            }
                            Node::Input(s) => {
                                if let Some(c_idx) = idx_map.get(s) {
                                    idx1 = *c_idx;
                                } else {
                                    idx1 = query_dag.add_node(QueryNode::Keyword(KeywordNode {
                                        keyword: s.to_string(),
                                        blk_height: end_blk_height,
                                        time_win: end_win_size,
                                    }));
                                    idx_map.insert(s.to_string(), idx1);
                                }
                            }
                        }
                        query_dag.add_edge(idx, idx1, ());
                        match &c2 {
                            Node::And(_) => {
                                idx2 = query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
                            }
                            Node::Or(_) => {
                                idx2 = query_dag.add_node(QueryNode::Union(UnionNode {}));
                            }
                            Node::Not(_) => {
                                idx2 = query_dag.add_node(QueryNode::Diff(DiffNode {}));
                            }
                            Node::Input(s) => {
                                if let Some(c_idx) = idx_map.get(s) {
                                    idx2 = *c_idx;
                                } else {
                                    idx2 = query_dag.add_node(QueryNode::Keyword(KeywordNode {
                                        keyword: s.to_string(),
                                        blk_height: end_blk_height,
                                        time_win: end_win_size,
                                    }));
                                    idx_map.insert(s.to_string(), idx2);
                                }
                            }
                        }
                        query_dag.add_edge(idx, idx2, ());
                        queue.push_back((c1, idx1));
                        queue.push_back((c2, idx2));
                    }
                    (Node::Or(n), idx) => {
                        let OrNode(c1, c2) = *n;
                        let idx1: NodeIndex;
                        let idx2: NodeIndex;
                        match &c1 {
                            Node::And(_) => {
                                idx1 = query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
                            }
                            Node::Or(_) => {
                                idx1 = query_dag.add_node(QueryNode::Union(UnionNode {}));
                            }
                            Node::Not(_) => {
                                idx1 = query_dag.add_node(QueryNode::Diff(DiffNode {}));
                            }
                            Node::Input(s) => {
                                if let Some(c_idx) = idx_map.get(s) {
                                    idx1 = *c_idx;
                                } else {
                                    idx1 = query_dag.add_node(QueryNode::Keyword(KeywordNode {
                                        keyword: s.to_string(),
                                        blk_height: end_blk_height,
                                        time_win: end_win_size,
                                    }));
                                    idx_map.insert(s.to_string(), idx1);
                                }
                            }
                        }
                        query_dag.add_edge(idx, idx1, ());
                        match &c2 {
                            Node::And(_) => {
                                idx2 = query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
                            }
                            Node::Or(_) => {
                                idx2 = query_dag.add_node(QueryNode::Union(UnionNode {}));
                            }
                            Node::Not(_) => {
                                idx2 = query_dag.add_node(QueryNode::Diff(DiffNode {}));
                            }
                            Node::Input(s) => {
                                if let Some(c_idx) = idx_map.get(s) {
                                    idx2 = *c_idx;
                                } else {
                                    idx2 = query_dag.add_node(QueryNode::Keyword(KeywordNode {
                                        keyword: s.to_string(),
                                        blk_height: end_blk_height,
                                        time_win: end_win_size,
                                    }));
                                    idx_map.insert(s.to_string(), idx2);
                                }
                            }
                        }
                        query_dag.add_edge(idx, idx2, ());
                        queue.push_back((c1, idx1));
                        queue.push_back((c2, idx2));
                    }
                    (Node::Not(n), idx) => {
                        let NotNode(c) = *n;
                        let c_idx: NodeIndex;
                        let blk_rt_idx = query_dag.add_node(QueryNode::BlkRt(BlkRtNode {
                            blk_height: end_blk_height,
                            time_win: end_win_size,
                        }));
                        match &c {
                            Node::And(_) => {
                                c_idx = query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
                            }
                            Node::Or(_) => {
                                c_idx = query_dag.add_node(QueryNode::Union(UnionNode {}));
                            }
                            Node::Not(_) => {
                                c_idx = query_dag.add_node(QueryNode::Diff(DiffNode {}));
                            }
                            Node::Input(s) => {
                                if let Some(ch_idx) = idx_map.get(s) {
                                    c_idx = *ch_idx;
                                } else {
                                    c_idx = query_dag.add_node(QueryNode::Keyword(KeywordNode {
                                        keyword: s.to_string(),
                                        blk_height: end_blk_height,
                                        time_win: end_win_size,
                                    }));
                                    idx_map.insert(s.to_string(), c_idx);
                                }
                            }
                        }
                        query_dag.add_edge(idx, c_idx, ());
                        query_dag.add_edge(idx, blk_rt_idx, ());
                        queue.push_back((c, c_idx));
                    }
                    (Node::Input(_), _idx) => {}
                }
            }
        } else {
            has_keyword_query = false;
        }

        if !self.range.is_empty() {
            has_range_query = true;
            let mut range_lock = false;
            for (i, r) in self.range.into_iter().enumerate() {
                // add range
                let range_idx = query_dag.add_node(QueryNode::Range(RangeNode {
                    range: r,
                    blk_height: end_blk_height,
                    time_win: end_win_size,
                    dim: i,
                }));
                if range_lock {
                    // add intersec
                    let intersec_idx = query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
                    query_dag.add_edge(intersec_idx, range_root_idx, ());
                    query_dag.add_edge(intersec_idx, range_idx, ());
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
            end_blk_idx = query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
            query_dag.add_edge(end_blk_idx, range_root_idx, ());
            query_dag.add_edge(end_blk_idx, keyword_root_idx, ());
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
            if self.start_blk > 1 {
                let blk_rt_idx = query_dag.add_node(QueryNode::BlkRt(BlkRtNode {
                    blk_height: Height(self.start_blk - 1),
                    time_win: size,
                }));
                let diff_idx = query_dag.add_node(QueryNode::Diff(DiffNode {}));
                query_dag.add_edge(diff_idx, blk_rt_idx, ());
                query_dag.add_edge(diff_idx, end_blk_idx, ());
            }
        }
        let res_query = Query {
            end_blk_height,
            query_dag,
        };
        let res_map = HashMap::<NodeIndex, HashSet<Digest>>::new();
        Ok((res_query, res_map))
    }
}

#[cfg(test)]
mod tests {
    use crate::chain::{
        query::{
            query_param::{Node, NotNode, OrNode, QueryParam},
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
        let time_wins: Vec<u64> = vec![4];
        let query_params = select_win_size(time_wins, query_param).unwrap();
        for (q_param, s_win_size, e_win_size) in query_params {
            let (query, _) = q_param.into_query_basic(s_win_size, e_win_size).unwrap();
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
        let time_wins: Vec<u64> = vec![4];
        let query_params = select_win_size(time_wins, query_param).unwrap();
        for (q_param, s_win_size, e_win_size) in query_params {
            let (query, _) = q_param.into_query_basic(s_win_size, e_win_size).unwrap();
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
        let time_wins: Vec<u64> = vec![4];
        let query_params = select_win_size(time_wins, query_param).unwrap();
        for (q_param, s_win_size, e_win_size) in query_params {
            let (query, _) = q_param.into_query_basic(s_win_size, e_win_size).unwrap();
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
        let time_wins: Vec<u64> = vec![4];
        let query_params = select_win_size(time_wins, query_param).unwrap();
        for (q_param, s_win_size, e_win_size) in query_params {
            let (query, _) = q_param.into_query_basic(s_win_size, e_win_size).unwrap();
            let query_dag = query.query_dag;
            println!("{:?}", Dot::with_config(&query_dag, &[Config::EdgeNoLabel]));
        }

        assert_eq!(1, 1);
    }
}
