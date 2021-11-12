use crate::{
    acc::{set::Set, AccValue},
    create_id_type_by_u32,
    digest::{Digest, Digestible},
};
use anyhow::Result;
use hash::{trie_leaf_hash, trie_non_leaf_node_hash, trie_non_leaf_root_hash};
use serde::{Deserialize, Serialize};
use smol_str::SmolStr;
use std::collections::BTreeMap;

create_id_type_by_u32!(TrieNodeId);

pub mod hash;
pub mod proof;
pub mod read;
pub mod write;

#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct TrieRoot {
    pub(crate) trie_root_id: Option<TrieNodeId>,
    pub(crate) trie_root_hash: Digest,
}

impl Digestible for TrieRoot {
    fn to_digest(&self) -> Digest {
        self.trie_root_hash
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum TrieNode {
    Leaf(TrieLeafNode),
    NonLeaf(TrieNonLeafNode),
    NonLeafRoot(TrieNonLeafRootNode),
}

impl Digestible for TrieNode {
    fn to_digest(&self) -> Digest {
        match self {
            TrieNode::Leaf(n) => n.to_digest(),
            TrieNode::NonLeaf(n) => n.to_digest(),
            TrieNode::NonLeafRoot(n) => n.to_digest(),
        }
    }
}

impl TrieNode {
    pub fn from_leaf(n: TrieLeafNode) -> Self {
        Self::Leaf(n)
    }

    pub fn from_non_leaf(n: TrieNonLeafNode) -> Self {
        Self::NonLeaf(n)
    }

    pub fn from_non_leaf_root(n: TrieNonLeafRootNode) -> Self {
        Self::NonLeafRoot(n)
    }

    pub fn get_id(&self) -> TrieNodeId {
        match self {
            TrieNode::Leaf(n) => n.id,
            TrieNode::NonLeaf(n) => n.id,
            TrieNode::NonLeafRoot(n) => n.id,
        }
    }

    pub fn get_string(&self) -> &str {
        match self {
            TrieNode::Leaf(n) => &n.rest,
            TrieNode::NonLeaf(n) => &n.nibble,
            TrieNode::NonLeafRoot(n) => &n.nibble,
        }
    }

    pub fn get_set(&self) -> &Set {
        match self {
            TrieNode::Leaf(n) => &n.data_set,
            TrieNode::NonLeaf(_) => panic!("Cannot read set from non-leaf node"),
            TrieNode::NonLeafRoot(n) => &n.data_set,
        }
    }

    pub fn get_acc(&self) -> &AccValue {
        match self {
            TrieNode::Leaf(n) => &n.data_set_acc,
            TrieNode::NonLeaf(_) => panic!("Cannot read set from non-leaf node"),
            TrieNode::NonLeafRoot(n) => &n.data_set_acc,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct TrieLeafNode {
    pub id: TrieNodeId,
    pub rest: SmolStr,
    pub data_set: Set,
    pub data_set_acc: AccValue,
}

impl Digestible for TrieLeafNode {
    fn to_digest(&self) -> Digest {
        trie_leaf_hash(&self.rest.to_digest(), &self.data_set_acc.to_digest())
    }
}

impl TrieLeafNode {
    pub fn new(rest: SmolStr, data_set: Set, data_set_acc: AccValue) -> Self {
        Self {
            id: TrieNodeId::next_id(),
            rest,
            data_set,
            data_set_acc,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct TrieNonLeafNode {
    pub id: TrieNodeId,
    pub nibble: SmolStr,
    pub children: BTreeMap<char, (TrieNodeId, Digest)>,
}

impl Digestible for TrieNonLeafNode {
    fn to_digest(&self) -> Digest {
        trie_non_leaf_node_hash(&self.nibble.to_digest(), self.children.iter())
    }
}

impl TrieNonLeafNode {
    pub fn new(nibble: SmolStr, children: BTreeMap<char, (TrieNodeId, Digest)>) -> Self {
        Self {
            id: TrieNodeId::next_id(),
            nibble,
            children,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct TrieNonLeafRootNode {
    pub id: TrieNodeId,
    pub nibble: SmolStr,
    pub data_set: Set,
    pub data_set_acc: AccValue,
    pub children: BTreeMap<char, (TrieNodeId, Digest)>,
}

impl Digestible for TrieNonLeafRootNode {
    fn to_digest(&self) -> Digest {
        trie_non_leaf_root_hash(
            &self.nibble.to_digest(),
            &self.data_set_acc.to_digest(),
            self.children.iter(),
        )
    }
}

impl TrieNonLeafRootNode {
    pub fn new(
        nibble: SmolStr,
        data_set: Set,
        data_set_acc: AccValue,
        children: BTreeMap<char, (TrieNodeId, Digest)>,
    ) -> Self {
        Self {
            id: TrieNodeId::next_id(),
            nibble,
            data_set,
            data_set_acc,
            children,
        }
    }
}

pub trait TrieNodeLoader {
    fn load_node(&self, id: TrieNodeId) -> Result<TrieNode>;
}

fn common_prefix_len(a: &str, b: &str) -> usize {
    a.chars().zip(b.chars()).take_while(|(a, b)| a == b).count()
}

fn split_at_common_prefix<'a>(a: &'a str, b: &'a str) -> (&'a str, &'a str, &'a str) {
    let prefix_len = common_prefix_len(a, b);
    let (common, remaining1) = a.split_at(prefix_len);
    let (_, remaining2) = b.split_at(prefix_len);
    (common, remaining1, remaining2)
}

fn split_at_common_prefix2(a: &str, b: &str) -> (String, char, String, char, String) {
    let (common, remain1, remain2) = split_at_common_prefix(a, b);
    let common = common;
    let first1;
    let first2;
    let remaining1: String;
    let remaining2: String;
    if remain1.is_empty() {
        first1 = '\0';
        remaining1 = "".to_string();
    } else {
        let (f1, r1) = remain1.split_at(1);
        first1 = f1.chars().next().expect("string is empty");
        remaining1 = r1.to_string();
    }

    if remain2.is_empty() {
        first2 = '\0';
        remaining2 = "".to_string();
    } else {
        let (f2, r2) = remain2.split_at(1);
        first2 = f2.chars().next().expect("string is empty");
        remaining2 = r2.to_string();
    }

    (common.to_string(), first1, remaining1, first2, remaining2)
}

#[cfg(test)]
mod tests;
