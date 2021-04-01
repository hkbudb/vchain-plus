use crate::digest::{Digest, Digestible};
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
        Self::from_subproof(SubProof::from_hash(root_hash))
    }

    pub fn root_hash(&self) -> Digest {
        match self.root.as_ref() {
            Some(root) => root.to_digest(),
            None => Digest::zero(),
        }
    }
}
