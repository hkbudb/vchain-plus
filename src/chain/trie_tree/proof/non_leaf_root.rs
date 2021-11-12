use std::collections::BTreeMap;

use crate::{
    acc::{AccPublicKey, AccValue, Set},
    chain::trie_tree::{hash::trie_non_leaf_root_proof_hash, split_at_common_prefix2, TrieNodeId},
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};
use smol_str::SmolStr;

use super::sub_proof::SubProof;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct TrieNonLeafRoot {
    pub(crate) nibble: String,
    pub(crate) acc_hash: Digest,
    pub(crate) children: BTreeMap<char, Box<SubProof>>,
}

impl Digestible for TrieNonLeafRoot {
    fn to_digest(&self) -> Digest {
        trie_non_leaf_root_proof_hash(
            &self.nibble.to_digest(),
            &self.acc_hash,
            self.children.iter(),
        )
    }
}

impl TrieNonLeafRoot {
    pub(crate) fn from_hashes(
        nibble: &str,
        acc_hash: &Digest,
        children: BTreeMap<char, Box<SubProof>>,
    ) -> Self {
        Self {
            nibble: nibble.to_string(),
            acc_hash: *acc_hash,
            children,
        }
    }

    pub(crate) fn value_acc_hash(&self, cur_key: &str, pk: &AccPublicKey) -> Digest {
        let (_common_key, cur_idx, rest_cur_key, _node_idx, _rest_node_key) =
            split_at_common_prefix2(cur_key, &self.nibble);
        match self.children.get(&cur_idx) {
            Some(c) => c.value_acc_hash(&rest_cur_key, pk),
            None => {
                let empty_set = Set::new();
                AccValue::from_set(&empty_set, pk).to_digest()
            }
        }
    }

    pub(crate) fn search_prefix(
        &mut self,
        cur_key: &str,
    ) -> Option<(*mut SubProof, Option<TrieNodeId>, SmolStr)> {
        let (_common_key, cur_idx, rest_cur_key, _node_idx, _rest_node_key) =
            split_at_common_prefix2(cur_key, &self.nibble);
        match self.children.get_mut(&cur_idx) {
            Some(child) => child.search_prefix(&rest_cur_key),
            None => None,
        }
    }

    pub(crate) fn remove_node_id(&mut self) {
        let children = &mut self.children;
        for c in children.values_mut() {
            let sub_proof = c.as_mut();
            sub_proof.remove_node_id();
        }
    }
}
