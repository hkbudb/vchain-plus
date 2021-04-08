use crate::{
    chain::{
        id_tree::{write::fanout_nary_rev, IdTreeObjId},
        IDTREE_FANOUT,
    },
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};

pub(crate) mod leaf;
pub(crate) use leaf::*;
pub(crate) mod non_leaf;
pub(crate) use non_leaf::*;
pub(crate) mod sub_proof;
pub(crate) use sub_proof::*;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Proof {
    pub(crate) root: Option<SubProof>,
}

impl Proof {
    pub fn new() -> Self {
        Self::default()
    }

    pub(crate) fn from_subproof(root: SubProof) -> Self {
        Self { root: Some(root) }
    }

    pub fn from_root_hash(root_hash: Digest) -> Self {
        if root_hash == Digest::zero() {
            Self::default()
        } else {
            Self::from_subproof(SubProof::from_hash(root_hash))
        }
    }

    // return the hash of the root for verification
    pub fn root_hash(&self) -> Digest {
        match self.root.as_ref() {
            Some(root) => root.to_digest(),
            None => Digest::zero(),
        }
    }

    // return the result leaf node hash (not obj_hash)
    pub fn value_hash(&self, obj_id: IdTreeObjId, n_k: usize) -> Option<Digest> {
        let depth = (n_k as f64).log(IDTREE_FANOUT as f64).floor() as usize;
        let mut cur_path_rev = fanout_nary_rev(obj_id.unwrap(), IDTREE_FANOUT as u64, depth);
        match self.root.as_ref() {
            None => Some(Digest::zero()),
            Some(root) => root.value_hash(obj_id, &mut cur_path_rev),
        }
    }
}
