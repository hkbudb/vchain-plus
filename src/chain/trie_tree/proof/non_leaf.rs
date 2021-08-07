use crate::{
    acc::{AccPublicKey, AccValue, Set},
    chain::trie_tree::{
        hash::trie_non_leaf_proof_hash,
        proof::{sub_proof::SubProof, TrieNodeId},
        split_at_common_prefix2,
    },
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};
use smol_str::SmolStr;
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
        nibble: &str,
        acc_val: AccValue,
        children: BTreeMap<char, Box<SubProof>>,
    ) -> Self {
        Self {
            nibble: nibble.to_string(),
            acc_val,
            children,
        }
    }

    pub(crate) fn value_acc(&self, cur_key: &str, pk: &AccPublicKey) -> AccValue {
        let (_common_key, cur_idx, rest_cur_key, _node_idx, _rest_node_key) =
            split_at_common_prefix2(&cur_key, &self.nibble);
        match self.children.get(&cur_idx) {
            Some(c) => c.value_acc(&rest_cur_key, pk),
            None => {
                let empty_set = Set::new();
                AccValue::from_set(&empty_set, pk)
            }
        }
    }

    pub(crate) fn search_prefix(
        &mut self,
        cur_key: &str,
    ) -> Option<(*mut SubProof, TrieNodeId, SmolStr)> {
        let (_common_key, cur_idx, rest_cur_key, _node_idx, _rest_node_key) =
            split_at_common_prefix2(&cur_key, &self.nibble);
        match self.children.get_mut(&cur_idx) {
            Some(child) => child.search_prefix(&rest_cur_key),
            None => None,
        }
    }
}
