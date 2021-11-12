use crate::{
    acc::{AccPublicKey, AccValue, Set},
    chain::trie_tree::TrieNodeId,
    digest::{Digest, Digestible},
};
use anyhow::{ensure, Result};
use serde::{Deserialize, Serialize};
use sub_proof::SubProof;

pub(crate) mod leaf;
pub(crate) mod non_leaf;
pub(crate) mod non_leaf_root;
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

    pub fn from_root_hash(root_id: Option<TrieNodeId>, nibble: &str, root_hash: Digest) -> Self {
        if root_hash == Digest::zero() {
            Self::default()
        } else {
            Self::from_subproof(SubProof::from_hash(root_id, nibble, root_hash))
        }
    }

    pub fn root_hash(&self) -> Digest {
        match self.root.as_ref() {
            Some(root) => root.to_digest(),
            None => Digest::zero(),
        }
    }

    fn value_acc_hash(&self, keyword: &str, pk: &AccPublicKey) -> Digest {
        match self.root.as_ref() {
            Some(root) => root.value_acc_hash(keyword, pk),
            None => {
                let empty_set = Set::new();
                AccValue::from_set(&empty_set, pk).to_digest()
            }
        }
    }

    pub fn verify_acc(&self, target_acc: AccValue, keyword: &str, pk: &AccPublicKey) -> Result<()> {
        let computed_acc = self.value_acc_hash(keyword, pk);
        ensure!(
            target_acc.to_digest() == computed_acc,
            "Trie verification: acc value not matched!"
        );
        Ok(())
    }

    pub(crate) fn remove_node_id(&mut self) {
        if let Some(sub_proof) = &mut self.root {
            sub_proof.remove_node_id();
        }
    }
}
