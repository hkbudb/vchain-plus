use super::{MAX_FANOUT, hash::{id_tree_leaf_hash, id_tree_non_leaf_hash}};
use crate::{create_id_type, digest::{Digest, Digestible}};
use smallvec::SmallVec;
use serde::{Serialize, Deserialize};


create_id_type!(IdTreeNodeId);
create_id_type!(IdTreeObjId);

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum IdTreeNode {
    Leaf(IdTreeLeafNode),
    NonLeaf(IdTreeNonLeafNode),
}

impl Digestible for IdTreeNode{
    fn to_digest(&self) -> Digest {
        match self {
            IdTreeNode::Leaf(n) => n.to_digest(),
            IdTreeNode::NonLeaf(n) => n.to_digest(),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct IdTreeLeafNode{
    pub id: IdTreeNodeId,
    pub obj_id: IdTreeObjId,
    pub obj_hash: Digest,
}

impl Digestible for IdTreeLeafNode{
    fn to_digest(&self) -> Digest {
        id_tree_leaf_hash(self.obj_id, &self.obj_hash)
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct IdTreeNonLeafNode{
    pub id: IdTreeNodeId,
    pub child_hashes: SmallVec<[Digest; MAX_FANOUT]>,
    pub child_ids: SmallVec<[IdTreeNodeId; MAX_FANOUT]>
}

impl Digestible for IdTreeNonLeafNode{
    fn to_digest(&self) -> Digest {
        id_tree_non_leaf_hash(self.child_hashes.iter())
    }
}
