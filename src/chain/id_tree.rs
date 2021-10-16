use crate::{
    chain::MAX_ININE_ID_FANOUT,
    create_id_type_by_u16, create_id_type_by_u32,
    digest::{Digest, Digestible},
};
use anyhow::Result;
use hash::{id_tree_leaf_hash, id_tree_non_leaf_hash, id_tree_root_hash};
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use std::num::NonZeroU16;

create_id_type_by_u32!(IdTreeNodeId);
create_id_type_by_u16!(IdTreeInternalId);

pub mod hash;
pub mod proof;
pub mod read;
pub mod write;

#[derive(
    Debug,
    Copy,
    Clone,
    Eq,
    PartialEq,
    Ord,
    PartialOrd,
    Hash,
    serde::Serialize,
    serde::Deserialize,
    derive_more::Deref,
    derive_more::DerefMut,
    derive_more::Display,
    derive_more::From,
    derive_more::Into,
)]
pub struct ObjId(pub NonZeroU16);

impl Digestible for ObjId {
    fn to_digest(&self) -> Digest {
        self.0.get().to_digest()
    }
}

impl ObjId {
    pub(crate) fn to_internal_id(self) -> IdTreeInternalId {
        IdTreeInternalId(self.0.get() - 1)
    }

    fn from_internal_id(id: IdTreeInternalId) -> Self {
        Self(unsafe { NonZeroU16::new_unchecked(id.0 + 1) })
    }
}

impl Default for ObjId {
    fn default() -> Self {
        Self(unsafe { NonZeroU16::new_unchecked(1) })
    }
}

#[derive(Debug, Copy, Clone, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct IdTreeRoot {
    id_tree_root_id: Option<IdTreeNodeId>,
    id_tree_root_hash: Digest,
    cur_obj_id: ObjId,
}

impl Digestible for IdTreeRoot {
    fn to_digest(&self) -> Digest {
        id_tree_root_hash(&self.cur_obj_id.to_digest(), &self.id_tree_root_hash)
    }
}

impl IdTreeRoot {
    pub(crate) fn get_id_tree_root_id(&self) -> Option<IdTreeNodeId> {
        self.id_tree_root_id
    }

    pub(crate) fn get_cur_obj_id(&self) -> ObjId {
        self.cur_obj_id
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum IdTreeNode {
    Leaf(IdTreeLeafNode),
    NonLeaf(Box<IdTreeNonLeafNode>),
}

impl IdTreeNode {
    pub fn get_node_id(&self) -> IdTreeNodeId {
        match self {
            IdTreeNode::Leaf(n) => n.id,
            IdTreeNode::NonLeaf(n) => n.id,
        }
    }

    pub fn from_leaf(l: IdTreeLeafNode) -> Self {
        Self::Leaf(l)
    }

    pub fn from_non_leaf(n: IdTreeNonLeafNode) -> Self {
        Self::NonLeaf(Box::new(n))
    }
}

impl Digestible for IdTreeNode {
    fn to_digest(&self) -> Digest {
        match self {
            IdTreeNode::Leaf(n) => n.to_digest(),
            IdTreeNode::NonLeaf(n) => n.to_digest(),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct IdTreeLeafNode {
    pub id: IdTreeNodeId,
    pub obj_id: IdTreeInternalId,
    pub obj_hash: Digest,
}

impl IdTreeLeafNode {
    fn new(obj_id: IdTreeInternalId, obj_hash: Digest) -> Self {
        Self {
            id: IdTreeNodeId::next_id(),
            obj_id,
            obj_hash,
        }
    }
}

impl Digestible for IdTreeLeafNode {
    fn to_digest(&self) -> Digest {
        id_tree_leaf_hash(self.obj_id, &self.obj_hash)
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct IdTreeNonLeafNode {
    pub id: IdTreeNodeId,
    pub child_hashes: SmallVec<[Digest; MAX_ININE_ID_FANOUT]>,
    pub child_ids: SmallVec<[IdTreeNodeId; MAX_ININE_ID_FANOUT]>,
}

impl IdTreeNonLeafNode {
    pub fn new(
        child_hashes: SmallVec<[Digest; MAX_ININE_ID_FANOUT]>,
        child_ids: SmallVec<[IdTreeNodeId; MAX_ININE_ID_FANOUT]>,
    ) -> Self {
        Self {
            id: IdTreeNodeId::next_id(),
            child_hashes,
            child_ids,
        }
    }

    pub fn new_ept() -> Self {
        Self {
            id: IdTreeNodeId::next_id(),
            child_hashes: SmallVec::new(),
            child_ids: SmallVec::new(),
        }
    }

    pub fn get_child_id(&self, idx: usize) -> Option<&IdTreeNodeId> {
        self.child_ids.get(idx)
    }

    pub fn get_child_id_mut(&mut self, idx: usize) -> Option<&mut IdTreeNodeId> {
        self.child_ids.get_mut(idx)
    }

    pub fn push_child_id(&mut self, id: IdTreeNodeId) {
        self.child_ids.push(id);
    }

    pub fn get_child_hash(&self, idx: usize) -> Option<&Digest> {
        self.child_hashes.get(idx)
    }

    pub fn get_child_hash_mut(&mut self, idx: usize) -> Option<&mut Digest> {
        self.child_hashes.get_mut(idx)
    }

    pub fn push_child_hash(&mut self, hash: Digest) {
        self.child_hashes.push(hash);
    }
}

impl Digestible for IdTreeNonLeafNode {
    fn to_digest(&self) -> Digest {
        id_tree_non_leaf_hash(self.child_hashes.iter())
    }
}
pub trait IdTreeNodeLoader {
    fn load_node(&self, id: IdTreeNodeId) -> Result<IdTreeNode>;
}

#[cfg(test)]
mod tests;
