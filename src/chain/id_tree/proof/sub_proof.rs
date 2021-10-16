use crate::{
    chain::id_tree::{
        proof::{leaf::IdTreeLeaf, non_leaf::IdTreeNonLeaf, sub_tree::IdTreeSubTree},
        IdTreeInternalId, IdTreeNodeId,
    },
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) enum SubProof {
    Hash(Box<IdTreeSubTree>),
    Leaf(Box<IdTreeLeaf>),
    NonLeaf(Box<IdTreeNonLeaf>),
}

impl Default for SubProof {
    fn default() -> Self {
        Self::Hash(Box::new(IdTreeSubTree::new(None, Digest::zero())))
    }
}

impl Digestible for SubProof {
    fn to_digest(&self) -> Digest {
        match self {
            Self::Hash(n) => n.get_node_hash(),
            Self::Leaf(n) => n.to_digest(),
            Self::NonLeaf(n) => n.to_digest(),
        }
    }
}

impl SubProof {
    pub(crate) fn from_hash(node_id: Option<IdTreeNodeId>, h: Digest) -> Self {
        Self::Hash(Box::new(IdTreeSubTree::new(node_id, h)))
    }

    pub(crate) fn from_non_leaf(n: IdTreeNonLeaf) -> Self {
        Self::NonLeaf(Box::new(n))
    }

    pub(crate) fn from_leaf(l: IdTreeLeaf) -> Self {
        Self::Leaf(Box::new(l))
    }

    pub(crate) fn value_hash(
        &self,
        obj_id: IdTreeInternalId,
        cur_path_rev: &mut Vec<usize>,
    ) -> Digest {
        match self {
            Self::Hash(_) => Digest::zero(),
            Self::Leaf(n) => n.value_hash(obj_id, cur_path_rev),
            Self::NonLeaf(n) => n.value_hash(obj_id, cur_path_rev),
        }
    }

    pub(crate) fn search_prefix<'a>(
        &mut self,
        obj_id: IdTreeInternalId,
        cur_path_rev: &'a mut Vec<usize>,
    ) -> Option<(*mut SubProof, Option<IdTreeNodeId>, &'a mut Vec<usize>)> {
        match self {
            Self::Hash(sub_tree) => {
                let node_id = sub_tree.node_id;
                Some((self as *mut _, node_id, cur_path_rev))
            }
            Self::NonLeaf(n) => n.search_prefix(obj_id, cur_path_rev),
            Self::Leaf(n) => {
                if obj_id == n.obj_id {
                    let node_id = n.node_id;
                    Some((self as *mut _, node_id, cur_path_rev))
                } else {
                    None
                }
            }
        }
    }

    pub(crate) fn remove_node_id(&mut self) {
        match self {
            Self::Hash(n) => {
                let sub_tree = n.as_mut();
                sub_tree.node_id = None;
            }
            Self::NonLeaf(n) => {
                let node = n.as_mut();
                node.remove_node_id();
            }
            Self::Leaf(n) => {
                let node = n.as_mut();
                node.node_id = None;
            }
        }
    }
}
