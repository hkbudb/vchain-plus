use super::MAX_INLINE_FANOUT;
use crate::{
    create_id_type,
    digest::{Digest, Digestible},
};
use anyhow::Result;
use hash::{id_tree_leaf_hash, id_tree_non_leaf_hash};
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
create_id_type!(IdTreeNodeId);
create_id_type!(IdTreeObjId);

pub mod hash;
pub mod proof;
pub mod read;
pub mod write;

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum IdTreeNode {
    Leaf(IdTreeLeafNode),
    NonLeaf(IdTreeNonLeafNode),
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
        Self::NonLeaf(n)
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
    pub obj_id: IdTreeObjId,
    pub obj_hash: Digest,
}

impl IdTreeLeafNode {
    fn new(obj_id: IdTreeObjId, obj_hash: Digest) -> Self {
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
    pub child_hashes: SmallVec<[Digest; MAX_INLINE_FANOUT]>,
    pub child_ids: SmallVec<[IdTreeNodeId; MAX_INLINE_FANOUT]>,
}

impl IdTreeNonLeafNode {
    pub fn new(
        child_hashes: SmallVec<[Digest; MAX_INLINE_FANOUT]>,
        child_ids: SmallVec<[IdTreeNodeId; MAX_INLINE_FANOUT]>,
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
            child_hashes: SmallVec::from_vec(vec![Digest::zero(); MAX_INLINE_FANOUT]),
            child_ids: SmallVec::from_vec(vec![IdTreeNodeId(0); MAX_INLINE_FANOUT]),
        }
    }

    pub fn get_child_id(&self, idx: usize) -> Option<&IdTreeNodeId> {
        self.child_ids.get(idx)
    }

    pub fn get_child_id_mut(&mut self, idx: usize) -> Option<&mut IdTreeNodeId> {
        self.child_ids.get_mut(idx)
    }

    pub fn get_child_hash(&self, idx: usize) -> Option<&Digest> {
        self.child_hashes.get(idx)
    }

    pub fn get_child_hash_mut(&mut self, idx: usize) -> Option<&mut Digest> {
        self.child_hashes.get_mut(idx)
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
