use super::{
    block_ads::{BlockADS, BlockMultiADS},
    bplus_tree::{BPlusTreeNode, BPlusTreeNodeId},
    hash::block_head_hash,
    id_tree::IdTreeNode,
    id_tree::IdTreeNodeId,
    trie_tree::{TrieNode, TrieTreeNodeId},
};
use crate::{
    create_id_type,
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};

create_id_type!(BlockId);

#[derive(Debug, Clone, Eq, PartialEq, Default, Serialize, Deserialize)]
pub struct BlockContent {
    pub block_id: BlockId,
    pub prev_hash: Digest,
    pub id_tree_root_id: IdTreeNodeId,
    pub id_tree_root_hash: Digest,
    pub ads: BlockMultiADS,
}

pub struct BlockHead {
    pub block_id: BlockId,
    pub prev_hash: Digest,
    pub id_tree_root_hash: Digest,
    pub ads_hash: Digest,
}

impl Digestible for BlockHead {
    fn to_digest(&self) -> Digest {
        // block_head_hash(self.block_id, &self.prev_hash, &self.id_tree_root_hash, &self.ads_hash)
        todo!()
    }
}
