use super::{
    super::{hash::trie_non_leaf_proof_hash, split_at_common_prefix2},
    sub_proof::SubProof,
    TrieNodeId,
};
use crate::{
    acc::{AccPublicKey, AccValue, Set},
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct TrieNonLeaf {
    pub(crate) nibble: String,
    pub(crate) acc_val: AccValue,
    pub(crate) children: BTreeMap<char, Box<SubProof>>,
}

impl Digestible for TrieNonLeaf {
    fn to_digest(&self) -> Digest {
        trie_non_leaf_proof_hash(
            &self.nibble.to_digest(),
            &self.acc_val.to_digest(),
            self.children.iter(),
        )
    }
}

impl TrieNonLeaf {
    pub(crate) fn from_hashes(
        nibble: String,
        acc_val: AccValue,
        children: BTreeMap<char, Box<SubProof>>,
    ) -> Self {
        Self {
            nibble,
            acc_val,
            children,
        }
    }

    pub(crate) fn value_acc(&self, cur_key: String, pk: &AccPublicKey) -> AccValue {
        let (_common_key, cur_idx, rest_cur_key, _node_idx, _rest_node_key) =
            split_at_common_prefix2(&cur_key, &self.nibble);
        match self.children.get(&cur_idx) {
            Some(c) => c.value_acc(rest_cur_key, pk),
            None => {
                let empty_set = Set::new();
                AccValue::from_set(&empty_set, pk)
            }
        }
    }

    pub(crate) fn search_prefix(
        &mut self,
        cur_key: String,
    ) -> Option<(*mut SubProof, TrieNodeId, String)> {
        let (_common_key, cur_idx, rest_cur_key, _node_idx, _rest_node_key) =
            split_at_common_prefix2(&cur_key, &self.nibble);
        match self.children.get_mut(&cur_idx) {
            Some(child) => child.search_prefix(rest_cur_key),
            None => None,
        }
    }
}
