use crate::{
    chain::trie_tree::TrieNodeId,
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub(crate) struct TrieSubTree {
    pub(crate) node_id: Option<TrieNodeId>,
    pub(crate) nibble: String,
    pub(crate) node_hash: Digest,
}

impl Digestible for TrieSubTree {
    fn to_digest(&self) -> Digest {
        self.node_hash
    }
}

impl TrieSubTree {
    pub(crate) fn new(node_id: Option<TrieNodeId>, nibble: &str, node_hash: Digest) -> Self {
        Self {
            node_id,
            nibble: nibble.to_string(),
            node_hash,
        }
    }
}
