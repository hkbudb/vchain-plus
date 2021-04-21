#![allow(unused)]
use super::{range::Range, traits::Num, MAX_FANOUT};
use crate::{
    acc::set::Set,
    create_id_type,
    digest::{Digest, Digestible},
};
use anyhow::Result;
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

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
pub enum BPlusTreeNode<K: Num> {
    Leaf(BPlusTreeLeafNode<K>),
    NonLeaf(BPlusTreeNonLeafNode<K>),
}

impl<K: Num> BPlusTreeNode<K> {
    pub fn get_node_id(&self) -> BPlusTreeNodeId {
        match self {
            BPlusTreeNode::Leaf(n) => n.id,
            BPlusTreeNode::NonLeaf(n) => n.id,
        }
    }

    pub fn get_node_hash(&self) -> Digest {
        match self {
            BPlusTreeNode::Leaf(n) => n.to_digest(),
            BPlusTreeNode::NonLeaf(n) => n.to_digest(),
        }
    }

    pub fn from_leaf(l: BPlusTreeLeafNode<K>) -> Self {
        Self::Leaf(l)
    }

    pub fn from_non_leaf(n: BPlusTreeNonLeafNode<K>) -> Self {
        Self::NonLeaf(n)
    }

    pub fn get_set(&self) -> Set {
        match self {
            BPlusTreeNode::Leaf(n) => n.data_set.clone(),
            BPlusTreeNode::NonLeaf(n) => n.data_set.clone(),
        }
    }

    pub fn get_range(&self) -> Range<K> {
        match self {
            BPlusTreeNode::Leaf(n) => Range::new(n.num, n.num),
            BPlusTreeNode::NonLeaf(n) => n.range,
        }
    }
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
    //pub data_set_acc: AccValue<E>,
}

impl<K: Num> Digestible for BPlusTreeLeafNode<K> {
    fn to_digest(&self) -> Digest {
        bplus_tree_leaf_hash(self.num /*, &self.data_set_acc.to_digest()*/)
    }
}

impl<K: Num> BPlusTreeLeafNode<K> {
    fn new(num: K, data_set: Set) -> Self {
        Self {
            id: BPlusTreeNodeId::next_id(),
            num,
            data_set,
            // cal_acc_val(&data_set),
        }
    }

    fn new_dbg(id: BPlusTreeNodeId, num: K, data_set: Set) -> Self {
        Self {
            id,
            num,
            data_set,
            // cal_acc_val(&data_set),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct BPlusTreeNonLeafNode<K: Num> {
    pub id: BPlusTreeNodeId,
    pub range: Range<K>,
    pub data_set: Set,
    //pub data_set_acc: AccValue<E>,
    pub child_hashes: SmallVec<[Digest; MAX_FANOUT]>,
    pub child_ids: SmallVec<[BPlusTreeNodeId; MAX_FANOUT]>,
}

impl<K: Num> BPlusTreeNonLeafNode<K> {
    pub fn new(
        range: Range<K>,
        data_set: Set,
        child_hashes: SmallVec<[Digest; MAX_FANOUT]>,
        child_ids: SmallVec<[BPlusTreeNodeId; MAX_FANOUT]>,
    ) -> Self {
        Self {
            id: BPlusTreeNodeId::next_id(),
            range,
            data_set,
            // data_set_acc: cal_acc_val(&data_set),
            child_hashes,
            child_ids,
        }
    }

    pub fn get_child_id(&self, idx: usize) -> Option<&BPlusTreeNodeId> {
        self.child_ids.get(idx)
    }

    pub fn get_child_id_mut(&mut self, idx: usize) -> Option<&mut BPlusTreeNodeId> {
        self.child_ids.get_mut(idx)
    }

    pub fn get_child_hash(&self, idx: usize) -> Option<&Digest> {
        self.child_hashes.get(idx)
    }

    pub fn get_child_hash_mut(&mut self, idx: usize) -> Option<&mut Digest> {
        self.child_hashes.get_mut(idx)
    }
}

impl<K: Num /*, E: PairingEngine*/> Digestible for BPlusTreeNonLeafNode<K /*, E*/> {
    fn to_digest(&self) -> Digest {
        bplus_tree_non_leaf_hash(
            &self.range,
            //&self.data_set_acc.to_digest(),
            self.child_hashes.iter(),
        )
    }
}

pub trait BPlusTreeNodeLoader<K: Num> {
    fn load_node(&self, id: BPlusTreeNodeId) -> Result<Option<BPlusTreeNode<K>>>;
}
