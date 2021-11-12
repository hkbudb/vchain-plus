use crate::{
    acc::{AccPublicKey, AccValue, Set},
    chain::trie_tree::{
        proof::{leaf::TrieLeaf, non_leaf::TrieNonLeaf, sub_tree::TrieSubTree},
        TrieNodeId,
    },
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};
use smol_str::SmolStr;

use super::non_leaf_root::TrieNonLeafRoot;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) enum SubProof {
    Hash(Box<TrieSubTree>),
    Leaf(Box<TrieLeaf>),
    NonLeaf(Box<TrieNonLeaf>),
    NonLeafRoot(Box<TrieNonLeafRoot>),
}

impl Default for SubProof {
    fn default() -> Self {
        Self::Hash(Box::new(TrieSubTree::new(None, "", Digest::zero())))
    }
}

impl Digestible for SubProof {
    fn to_digest(&self) -> Digest {
        match self {
            Self::Hash(n) => n.to_digest(),
            Self::Leaf(n) => n.to_digest(),
            Self::NonLeaf(n) => n.to_digest(),
            Self::NonLeafRoot(n) => n.to_digest(),
        }
    }
}

impl SubProof {
    pub(crate) fn from_hash(node_id: Option<TrieNodeId>, nibble: &str, node_hash: Digest) -> Self {
        Self::Hash(Box::new(TrieSubTree::new(node_id, nibble, node_hash)))
    }

    pub(crate) fn from_non_leaf(n: TrieNonLeaf) -> Self {
        Self::NonLeaf(Box::new(n))
    }

    pub(crate) fn from_non_leaf_root(n: TrieNonLeafRoot) -> Self {
        Self::NonLeafRoot(Box::new(n))
    }

    pub(crate) fn from_leaf(l: TrieLeaf) -> Self {
        Self::Leaf(Box::new(l))
    }

    pub(crate) fn value_acc_hash(&self, cur_key: &str, pk: &AccPublicKey) -> Digest {
        match self {
            SubProof::Hash(_) => {
                let empty_set = Set::new();
                AccValue::from_set(&empty_set, pk).to_digest()
            }
            SubProof::Leaf(n) => n.value_acc_hash(cur_key, pk),
            SubProof::NonLeaf(n) => n.value_acc_hash(cur_key, pk),
            SubProof::NonLeafRoot(n) => n.value_acc_hash(cur_key, pk),
        }
    }

    pub(crate) fn search_prefix<'a>(
        &'a mut self,
        cur_key: &'a str,
    ) -> Option<(*mut SubProof, Option<TrieNodeId>, SmolStr)> {
        match self {
            SubProof::Hash(sub_tree) => {
                let node_id = sub_tree.node_id;
                Some((self as *mut _, node_id, SmolStr::from(cur_key)))
            }
            SubProof::Leaf(n) => {
                if n.rest == cur_key {
                    let node_id = n.node_id;
                    Some((self as *mut _, node_id, SmolStr::from(cur_key)))
                } else {
                    None
                }
            }
            SubProof::NonLeaf(n) => n.search_prefix(cur_key),
            SubProof::NonLeafRoot(n) => n.search_prefix(cur_key),
        }
    }

    pub(crate) fn remove_node_id(&mut self) {
        match self {
            SubProof::Hash(n) => {
                let sub_tree = n.as_mut();
                sub_tree.node_id = None;
            }
            SubProof::Leaf(n) => {
                let leaf = n.as_mut();
                leaf.node_id = None;
            }
            SubProof::NonLeaf(n) => {
                let node = n.as_mut();
                node.remove_node_id();
            }
            SubProof::NonLeafRoot(n) => {
                let node = n.as_mut();
                node.remove_node_id();
            }
        }
    }
}
