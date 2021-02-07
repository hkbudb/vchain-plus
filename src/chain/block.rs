use super::{
    bplus_tree::BPlusTreeNode, hash::block_header_hash, id_tree::IdTreeNode, traits::Num,
    trie_tree::TrieNode, INDEX_NUM,
};
use crate::{
    acc::set::Set,
    create_id_type,
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

create_id_type!(BlockId);

#[derive(Debug, Clone, Eq, PartialEq, Default, Serialize, Deserialize)]
pub struct BlockHeader {
    pub block_id: BlockId,
    pub prev_hash: Digest,
    pub id_root_dig: Digest,
    pub ads_root_dig: SmallVec<[Digest; INDEX_NUM]>, // for multi-k index
    pub data_set: Set,
    // pub data_set_acc: ***
}

impl Digestible for BlockHeader {
    fn to_digest(&self) -> Digest {
        // block_header_hash(self.block_id, &self.prev_hash, &self.id_root_dig, &ads_root_dig.iter(), &self.data_set_acc)
        todo!()
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct BlockContent<K: Num> {
    pub block_id: BlockId,
    pub id_tree: IdTreeNode,                                  // id tree root
    pub bplus_trees: SmallVec<[BPlusTreeNode<K>; INDEX_NUM]>, // bplus tree root
    pub trie_tree: TrieNode,                                  // trie root
}
