//use super::INLINE_FANOUT;
use crate::{
    acc::set::Set,
    create_id_type,
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};
//use smallvec::SmallVec;

create_id_type!(TrieTreeNodeId);

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum TrieNode {
    Leaf(TrieLeafNode),
    NonLeaf(TrieNonLeafNode),
}

impl TrieNode {
    pub fn get_node_id(&self) -> TrieTreeNodeId {
        match self {
            TrieNode::Leaf(n) => n.id,
            TrieNode::NonLeaf(n) => n.id,
        }
    }
}

impl Digestible for TrieNode {
    fn to_digest(&self) -> Digest {
        match self {
            TrieNode::Leaf(n) => n.to_digest(),
            TrieNode::NonLeaf(n) => n.to_digest(),
        }
    }
}
#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct TrieLeafNode {
    pub id: TrieTreeNodeId,
    pub data_set: Set,
    //pub data_set_acc: ***,
}

impl Digestible for TrieLeafNode {
    fn to_digest(&self) -> Digest {
        todo!()
        // trie_leaf_hash(self.data_set_acc.to_digest())
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct TrieNonLeafNode {
    pub id: TrieTreeNodeId,
    pub nibble: String,
    pub data_set: Set,
    //pub data_set_acc: ***,
    //pub children: BTreeMap<char, (ID, digest))> // nibble + char + children's rest, use smol_str, ref: https://github.com/rust-analyzer/smol_str
}

impl Digestible for TrieNonLeafNode {
    fn to_digest(&self) -> Digest {
        todo!()
        // trie_non_leaf_hash(&self.nibble, &self.data_set_acc,to_digest(), self.child_hashes.iter())
    }
}
