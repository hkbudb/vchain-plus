use super::{
    hash::{bplus_tree_leaf_hash, bplus_tree_non_leaf_hash},
    range::Range,
    traits::Num,
    MAX_FANOUT,
};
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

impl<K: Num> Digestible for BPlusTreeNode<K> {
    fn to_digest(&self) -> Digest {
        match self {
            BPlusTreeNode::Leaf(n) => n.to_digest(),
            BPlusTreeNode::NonLeaf(n) => n.to_digest(),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct BPlusTreeLeafNode<K: Num> {
    pub id: BPlusTreeNodeId,
    pub num: K,
    pub data_set: Set,
    //pub data_set_acc: ***,
}

impl<K: Num> Digestible for BPlusTreeLeafNode<K> {
    fn to_digest(&self) -> Digest {
        todo!()
        //bplus_tree_leaf_hash(self.num, &self.data_set_acc.to_digest())
    }
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

impl<K: Num> Digestible for BPlusTreeNonLeafNode<K> {
    fn to_digest(&self) -> Digest {
        todo!()
        // bplus_tree_non_leaf_hash(&self.range, &self.data_set_acc.to_digest(), self.child_hashes.iter())
    }
}
