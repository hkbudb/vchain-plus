use super::TrieNodeId;
use crate::{
    acc::{AccValue, Set},
    chain::PUB_KEY,
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};
use sub_proof::SubProof;

pub(crate) mod leaf;
pub(crate) mod non_leaf;
pub(crate) mod sub_proof;
pub(crate) mod sub_tree;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Proof {
    pub(crate) root: Option<SubProof>,
}

impl Proof {
    pub fn new() -> Self {
        Self::default()
    }

    pub(crate) fn from_subproof(root: SubProof) -> Self {
        Self { root: Some(root) }
    }

    pub fn from_root_hash(root_id: TrieNodeId, nibble: String, root_hash: Digest) -> Self {
        if root_hash == Digest::zero() {
            Self::default()
        } else {
            Self::from_subproof(SubProof::from_hash(root_id, nibble, root_hash))
        }
    }

    // return the hash of the root for verification
    pub fn root_hash(&self) -> Digest {
        match self.root.as_ref() {
            Some(root) => root.to_digest(),
            None => Digest::zero(),
        }
    }

    // return the acc of the result set based on keyword
    pub fn value_acc(&self, keyword: String) -> AccValue {
        match self.root.as_ref() {
            Some(root) => root.value_acc(keyword),
            None => {
                let empty_set = Set::new();
                AccValue::from_set(&empty_set, &PUB_KEY)
            }
        }
    }
}
