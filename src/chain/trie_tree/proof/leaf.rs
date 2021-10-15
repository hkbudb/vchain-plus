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
    pub(crate) acc_val: AccValue,
}

impl Digestible for TrieLeaf {
    fn to_digest(&self) -> Digest {
        trie_leaf_proof_hash(&self.rest.to_digest(), &self.acc_val.to_digest())
    }
}

impl TrieLeaf {
    pub(crate) fn new(node_id: Option<TrieNodeId>, rest: &str, acc_val: AccValue) -> Self {
        Self {
            node_id,
            rest: rest.to_string(),
            acc_val,
        }
    }

    pub(crate) fn value_acc(&self, cur_key: &str, pk: &AccPublicKey) -> AccValue {
        if cur_key == self.rest {
            self.acc_val
        } else {
            let empty_set = Set::new();
            AccValue::from_set(&empty_set, pk)
        }
    }
}
