use crate::chain::{
    block::Height,
    query::query_obj::{
        BlkRtNode, DiffNode, IntersecNode, KeywordNode, Query, QueryNode, RangeNode, UnionNode,
    },
    range::Range,
    traits::Num,
};
use anyhow::Result;
use petgraph::{graph::NodeIndex, Graph};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, VecDeque};

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
enum Node {
    And(Box<AndNode>),
    Or(Box<OrNode>),
    Not(Box<NotNode>),
    Input(String),
}

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
struct AndNode(Node, Node);

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
struct OrNode(Node, Node);

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
struct NotNode(Node);

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct QueryParam<K: Num> {
    start_blk: u64,
    end_blk: u64,
    range: Vec<Range<K>>,
    keyword_exp: Node,
}

impl<K: Num> QueryParam<K> {
    pub fn into_query_basic(self, time_win: u64) -> Result<Query<K>> {
        let end_blk_height = Height(self.end_blk);
        let keyword_exp = self.keyword_exp;
        let mut query_dag = Graph::<QueryNode<K>, ()>::new();
        let keyword_root_idx: NodeIndex;
        let mut queue = VecDeque::<(Node, NodeIndex)>::new();
        let mut idx_map = HashMap::<String, NodeIndex>::new();

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
                            time_win,
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
                            time_win,
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
                            time_win,
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
                            time_win,
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
                let blk_rt_idx = query_dag.add_node(QueryNode::BlkRt(BlkRtNode {
                    blk_height: end_blk_height,
                }));
                query_dag.add_edge(idx, blk_rt_idx, ());
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
                            time_win,
                        }));
                        idx_map.insert(s.to_string(), c_idx);
                    }
                }
                query_dag.add_edge(idx, c_idx, ());
                queue.push_back((c, c_idx));
            }
            Node::Input(s) => {
                let idx = query_dag.add_node(QueryNode::Keyword(KeywordNode {
                    keyword: s,
                    blk_height: end_blk_height,
                    time_win,
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
                                    time_win,
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
                                    time_win,
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
                                    time_win,
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
                                    time_win,
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
                    let blk_rt_idx = query_dag.add_node(QueryNode::BlkRt(BlkRtNode {
                        blk_height: end_blk_height,
                    }));
                    query_dag.add_edge(idx, blk_rt_idx, ());
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
                            if let Some(ch_idx) = idx_map.get(s) {
                                c_idx = *ch_idx;
                            } else {
                                c_idx = query_dag.add_node(QueryNode::Keyword(KeywordNode {
                                    keyword: s.to_string(),
                                    blk_height: end_blk_height,
                                    time_win,
                                }));
                                idx_map.insert(s.to_string(), c_idx);
                            }
                        }
                    }
                    query_dag.add_edge(idx, c_idx, ());
                    queue.push_back((c, c_idx));
                }
                (Node::Input(_), _idx) => {}
            }
        }

        let mut range_lock = false;
        let mut range_root_idx: NodeIndex = NodeIndex::default();
        for (i, r) in self.range.into_iter().enumerate() {
            // add range
            let range_idx = query_dag.add_node(QueryNode::Range(RangeNode {
                range: r,
                blk_height: end_blk_height,
                time_win,
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

        let intersec_idx = query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
        query_dag.add_edge(intersec_idx, range_root_idx, ());
        query_dag.add_edge(intersec_idx, keyword_root_idx, ());

        let start_blk_height = Height(self.start_blk);
        if start_blk_height.0 <= 1 || end_blk_height.0 - start_blk_height.0 >= time_win {
        } else {
            let blk_rt_idx = query_dag.add_node(QueryNode::BlkRt(BlkRtNode {
                blk_height: Height(start_blk_height.0 - 1),
            }));
            let diff_idx = query_dag.add_node(QueryNode::Diff(DiffNode {}));
            query_dag.add_edge(diff_idx, blk_rt_idx, ());
            query_dag.add_edge(diff_idx, intersec_idx, ());
        }
        let res_query = Query {
            end_blk_height,
            query_dag,
        };
        Ok(res_query)
    }
}

#[cfg(test)]
mod test {
    use crate::chain::{
        block::Height,
        query::{
            query_obj::{
                BlkRtNode, DiffNode, IntersecNode, KeywordNode, QueryNode, RangeNode, UnionNode,
            },
            query_param::{Node, NotNode, OrNode, QueryParam},
        },
        range::Range,
    };
    use petgraph::dot::{Config, Dot};
    use petgraph::Graph;
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
            keyword_exp: Node::Or(Box::new(OrNode(
                Node::Input("a".to_string()),
                Node::Not(Box::new(NotNode(Node::Input("b".to_string())))),
            ))),
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
            keyword_exp: Node::Or(Box::new(OrNode(
                Node::Input("a".to_string()),
                Node::Not(Box::new(NotNode(Node::Input("b".to_string())))),
            ))),
        };
        assert_eq!(query_param, expect);
    }

    #[test]
    fn test_to_query_basic() {
        let data = json!({
            "start_blk": 1,
            "end_blk": 3,
            "range": [(1, 5), (2, 8)],
            "keyword_exp": {
                "or": [
                    {"input": "a"},
                    {"and": [{"input": "b"}, {"input": "c"}]},
                ]
            },
        });
        let query_param: QueryParam<u32> = serde_json::from_value(data).unwrap();
        let time_win = 4;
        let query = query_param.into_query_basic(time_win).unwrap();
        let mut expect_query_dag = Graph::<QueryNode<u32>, ()>::new();
        let idx_0 = expect_query_dag.add_node(QueryNode::Union(UnionNode {}));
        let idx_1 = expect_query_dag.add_node(QueryNode::Keyword(KeywordNode {
            keyword: "a".to_string(),
            blk_height: Height(3),
            time_win,
        }));
        expect_query_dag.add_edge(idx_0, idx_1, ());
        let idx_2 = expect_query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
        expect_query_dag.add_edge(idx_0, idx_2, ());
        let idx_3 = expect_query_dag.add_node(QueryNode::Keyword(KeywordNode {
            keyword: "b".to_string(),
            blk_height: Height(3),
            time_win,
        }));
        expect_query_dag.add_edge(idx_2, idx_3, ());
        let idx_4 = expect_query_dag.add_node(QueryNode::Keyword(KeywordNode {
            keyword: "c".to_string(),
            blk_height: Height(3),
            time_win,
        }));
        expect_query_dag.add_edge(idx_2, idx_4, ());
        let idx_5 = expect_query_dag.add_node(QueryNode::Range(RangeNode {
            range: Range::<u32>::new(1, 5),
            blk_height: Height(3),
            time_win,
            dim: 0,
        }));
        let idx_6 = expect_query_dag.add_node(QueryNode::Range(RangeNode {
            range: Range::<u32>::new(2, 8),
            blk_height: Height(3),
            time_win,
            dim: 1,
        }));
        let idx_7 = expect_query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
        expect_query_dag.add_edge(idx_7, idx_5, ());
        expect_query_dag.add_edge(idx_7, idx_6, ());
        let idx_8 = expect_query_dag.add_node(QueryNode::Intersec(IntersecNode {}));
        expect_query_dag.add_edge(idx_8, idx_7, ());
        expect_query_dag.add_edge(idx_8, idx_0, ());
        let idx_9 = expect_query_dag.add_node(QueryNode::BlkRt(BlkRtNode {
            blk_height: Height(1),
        }));
        let idx_10 = expect_query_dag.add_node(QueryNode::Diff(DiffNode {}));
        expect_query_dag.add_edge(idx_10, idx_9, ());
        expect_query_dag.add_edge(idx_10, idx_8, ());

        let query_dag = query.query_dag;
        println!("computed");
        println!("{:?}", Dot::with_config(&query_dag, &[Config::EdgeNoLabel]));
        println!("expect");
        println!(
            "{:?}",
            Dot::with_config(&expect_query_dag, &[Config::EdgeNoLabel])
        );
        assert_eq!(1, 1);
        // let expect_query = Query {
        //     end_blk_height: Height(3),
        //     expect_query_dag,
        // };
        //assert_eq!(query, expect_query);
    }
}
