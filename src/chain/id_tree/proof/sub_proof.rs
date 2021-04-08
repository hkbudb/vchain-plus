use super::{IdTreeLeaf, IdTreeNonLeaf};
use crate::{
    chain::id_tree::IdTreeObjId,
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) enum SubProof {
    Hash(Digest),
    Leaf(Box<IdTreeLeaf>),
    NonLeaf(Box<IdTreeNonLeaf>),
}

impl Default for SubProof {
    fn default() -> Self {
        Self::Hash(Digest::zero())
    }
}

impl Digestible for SubProof {
    fn to_digest(&self) -> Digest {
        match self {
            Self::Hash(n) => *n,
            Self::Leaf(n) => n.to_digest(),
            Self::NonLeaf(n) => n.to_digest(),
        }
    }
}

impl SubProof {
    pub(crate) fn from_hash(h: Digest) -> Self {
        Self::Hash(h)
    }

    pub(crate) fn from_non_leaf(n: IdTreeNonLeaf) -> Self {
        Self::NonLeaf(Box::new(n))
    }

    pub(crate) fn from_leaf(l: IdTreeLeaf) -> Self {
        Self::Leaf(Box::new(l))
    }

    pub(crate) fn value_hash(
        &self,
        obj_id: IdTreeObjId,
        cur_path_rev: &mut Vec<usize>,
    ) -> Option<Digest> {
        match self {
            Self::Hash(_) => None,
            Self::Leaf(n) => n.value_hash(obj_id, cur_path_rev),
            Self::NonLeaf(n) => n.value_hash(obj_id, cur_path_rev),
        }
    }

    pub(crate) fn search_prefix<'a>(
        &mut self,
        obj_id: IdTreeObjId,
        cur_path_rev: &'a mut Vec<usize>,
    ) -> Option<(*mut SubProof, Digest, &'a mut Vec<usize>)>{
        match self {
            Self::Hash(h) => {
                let hash = *h;
                Some((self as *mut _, hash, cur_path_rev))
            }
            Self::NonLeaf(n) => {
                n.search_prefix(obj_id, cur_path_rev)
            }
            Self::Leaf(n) => {
                if obj_id == n.obj_id {
                    let n_hash = n.to_digest();
                    Some((self as *mut _, n_hash, cur_path_rev))
                } else {
                    None
                }
            }
        }
    }
}
