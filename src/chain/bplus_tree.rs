use super::{range::Range, types::Num, MAX_FANOUT};
use crate::{
    acc::set::Set,
    create_id_type,
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

create_id_type!(BPlusTreeNodeId);

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum BPlusTreeNode<K: Num> {
    Leaf(BPlusTreeLeafNode<K>),
    NonLeaf(BPlusTreeNonLeafNode<K>),
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct BPlusTreeLeafNode<K: Num> {
    pub id: BPlusTreeNodeId,
    pub num: K,
    pub data_set: Set,
    //pub data_set_acc: ***,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct BPlusTreeNonLeafNode<K: Num> {
    pub id: BPlusTreeNodeId,
    pub range: Range<K>,
    pub data_set: Set,
    // pub data_set_acc: ***,
    pub child_hashes: SmallVec<[Digest; MAX_FANOUT]>,
    pub child_ids: SmallVec<[BPlusTreeNodeId; MAX_FANOUT]>,
}
