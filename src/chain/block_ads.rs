use std::collections::HashMap;

use super::{bplus_tree::BPlusTreeNodeId, trie_tree::TrieTreeNodeId};
use crate::digest::Digest;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Eq, PartialEq, Default, Serialize, Deserialize)]
pub struct BlockADS {
    pub bplus_tree_root_ids: Vec<BPlusTreeNodeId>,
    pub bplus_tree_root_hashes: Vec<Digest>,
    pub trie_root_id: TrieTreeNodeId,
    pub trie_root_hash: Digest,
}

#[derive(Debug, Clone, Eq, PartialEq, Default, Serialize, Deserialize)]
pub struct BlockMultiADS(HashMap<u64, BlockADS>); // time window - BlockAds map
