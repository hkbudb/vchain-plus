use super::{
    //hash::{bplus_tree_leaf_hash, bplus_tree_non_leaf_hash},
    range::Range,
    traits::Num,
    MAX_FANOUT,
};
use crate::{
    acc::{set::Set, acc_value::AccValue},
    create_id_type,
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use ark_ec::PairingEngine;

create_id_type!(BPlusTreeNodeId);

pub mod read;
pub use read::*;
pub mod write;
pub use write::*;
pub mod proof;
pub use proof::*;
pub mod hash;
pub use hash::*;
pub mod tests;
pub use tests::*;

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum BPlusTreeNode<K: Num, E: PairingEngine> {
    Leaf(BPlusTreeLeafNode<K, E>),
    NonLeaf(BPlusTreeNonLeafNode<K, E>),
}

impl<K: Num, E: PairingEngine> BPlusTreeNode<K, E> {
    pub fn get_node_id(&self) -> BPlusTreeNodeId {
        match self {
            BPlusTreeNode::Leaf(n) => n.id,
            BPlusTreeNode::NonLeaf(n) => n.id,
        }
    }
}

impl<K: Num, E: PairingEngine> Digestible for BPlusTreeNode<K, E> {
    fn to_digest(&self) -> Digest {
        match self {
            BPlusTreeNode::Leaf(n) => n.to_digest(),
            BPlusTreeNode::NonLeaf(n) => n.to_digest(),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct BPlusTreeLeafNode<K: Num, E: PairingEngine> {
    pub id: BPlusTreeNodeId,
    pub num: K,
    pub data_set: Set,
    pub data_set_acc: AccValue<E>,
}

impl<K: Num, E: PairingEngine> Digestible for BPlusTreeLeafNode<K, E> {
    fn to_digest(&self) -> Digest {
        bplus_tree_leaf_hash(self.num, &self.data_set_acc.to_digest())
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct BPlusTreeNonLeafNode<K: Num, E: PairingEngine> {
    pub id: BPlusTreeNodeId,
    pub range: Range<K>,
    pub data_set: Set,
    pub data_set_acc: AccValue<E>,
    pub child_hashes: SmallVec<[Digest; MAX_FANOUT]>,
    pub child_ids: SmallVec<[BPlusTreeNodeId; MAX_FANOUT]>,
}

impl<K: Num, E: PairingEngine> Digestible for BPlusTreeNonLeafNode<K, E> {
    fn to_digest(&self) -> Digest {
        bplus_tree_non_leaf_hash(&self.range, &self.data_set_acc.to_digest(), self.child_hashes.iter())
    }
}
