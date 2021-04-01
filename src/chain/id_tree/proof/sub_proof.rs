use super::{IdTreeLeaf, IdTreeNonLeaf};
use crate::digest::{Digest, Digestible};
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
}
