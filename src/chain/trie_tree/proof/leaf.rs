use crate::{
    acc::{AccPublicKey, AccValue, Set},
    chain::trie_tree::{hash::trie_leaf_proof_hash, TrieNodeId},
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct TrieLeaf {
    pub(crate) node_id: Option<TrieNodeId>,
    pub(crate) rest: String,
    pub(crate) acc_hash: Digest,
}

impl Digestible for TrieLeaf {
    fn to_digest(&self) -> Digest {
        trie_leaf_proof_hash(&self.rest.to_digest(), &self.acc_hash)
    }
}

impl TrieLeaf {
    pub(crate) fn new(node_id: Option<TrieNodeId>, rest: &str, acc_hash: Digest) -> Self {
        Self {
            node_id,
            rest: rest.to_string(),
            acc_hash,
        }
    }

    pub(crate) fn value_acc_hash(&self, cur_key: &str, pk: &AccPublicKey) -> Digest {
        if cur_key == self.rest {
            self.acc_hash
        } else {
            let empty_set = Set::new();
            AccValue::from_set(&empty_set, pk).to_digest()
        }
    }
}
