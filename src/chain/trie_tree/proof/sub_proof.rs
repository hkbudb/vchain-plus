use super::{super::TrieNodeId, leaf::TrieLeaf, non_leaf::TrieNonLeaf, sub_tree::TrieSubTree};
use crate::{
    acc::{AccValue, Set},
    chain::PUB_KEY,
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) enum SubProof {
    Hash(Box<TrieSubTree>),
    Leaf(Box<TrieLeaf>),
    NonLeaf(Box<TrieNonLeaf>),
}

impl Default for SubProof {
    fn default() -> Self {
        Self::Hash(Box::new(TrieSubTree::new(
            TrieNodeId(0),
            "".to_string(),
            Digest::zero(),
        )))
    }
}

impl Digestible for SubProof {
    fn to_digest(&self) -> Digest {
        match self {
            Self::Hash(n) => n.to_digest(),
            Self::Leaf(n) => n.to_digest(),
            Self::NonLeaf(n) => n.to_digest(),
        }
    }
}

impl SubProof {
    pub(crate) fn from_hash(node_id: TrieNodeId, nibble: String, node_hash: Digest) -> Self {
        Self::Hash(Box::new(TrieSubTree::new(node_id, nibble, node_hash)))
    }

    pub(crate) fn from_non_leaf(n: TrieNonLeaf) -> Self {
        Self::NonLeaf(Box::new(n))
    }

    pub(crate) fn from_leaf(l: TrieLeaf) -> Self {
        Self::Leaf(Box::new(l))
    }

    pub(crate) fn value_acc(&self, cur_key: String) -> AccValue {
        match self {
            SubProof::Hash(_) => {
                let empty_set = Set::new();
                AccValue::from_set(&empty_set, &PUB_KEY)
            }
            SubProof::Leaf(n) => n.value_acc(cur_key),
            SubProof::NonLeaf(n) => n.value_acc(cur_key),
        }
    }

    pub(crate) fn search_prefix(
        &mut self,
        cur_key: String,
    ) -> Option<(*mut SubProof, TrieNodeId, String)> {
        match self {
            SubProof::Hash(sub_tree) => {
                let node_id = sub_tree.node_id;
                Some((self as *mut _, node_id, cur_key))
            }
            SubProof::Leaf(n) => {
                if n.rest == cur_key {
                    let node_id = n.node_id;
                    Some((self as *mut _, node_id, cur_key))
                } else {
                    None
                }
            }
            SubProof::NonLeaf(n) => n.search_prefix(cur_key),
        }
    }
}
