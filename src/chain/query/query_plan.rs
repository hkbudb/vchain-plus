use crate::{
    acc::{set::Set, AccValue},
    chain::{block::Height, bplus_tree, range::Range, traits::Num, trie_tree},
};
use petgraph::{graph::NodeIndex, Graph};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Serialize, Deserialize)]
pub enum QPNode<K: Num> {
    Range(QPRangeNode<K>),
    Keyword(Box<QPKeywordNode>),
    BlkRt(Box<QPBlkRtNode>),
    Union(QPUnion),
    Intersec(QPIntersec),
    Diff(QPDiff),
}

#[derive(Debug, Serialize, Deserialize)]
pub struct QPRangeNode<K: Num> {
    pub(crate) range: Range<K>,
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
    pub(crate) dim: usize,
    pub(crate) set: Option<(Set, AccValue, u32, u32)>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct QPKeywordNode {
    pub(crate) keyword: String,
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
    pub(crate) set: Option<(Set, AccValue, u32, u32)>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct QPBlkRtNode {
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
    pub(crate) set: Option<(Set, u32, u32)>,
    pub(crate) acc: Option<AccValue>,
}

#[derive(Default, Debug, Serialize, Deserialize)]
pub struct QPUnion {
    pub(crate) set: Option<(Set, u32, u32)>,
}

#[derive(Default, Debug, Serialize, Deserialize)]
pub struct QPIntersec {
    pub(crate) set: Option<(Set, u32, u32)>,
}

#[derive(Default, Debug, Serialize, Deserialize)]
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
