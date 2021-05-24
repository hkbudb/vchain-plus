use super::{super::hash::bplus_tree_non_leaf_proof_hash, sub_proof::SubProof};
use crate::digest::Digest;
use crate::{
    acc::AccValue,
    chain::{range::Range, traits::Num, MAX_INLINE_FANOUT},
    digest::Digestible,
};
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct BPlusTreeNonLeaf<K: Num> {
    pub(crate) range: Range<K>,
    pub(crate) acc_val: AccValue,
    pub(crate) children: SmallVec<[Option<Box<SubProof<K>>>; MAX_INLINE_FANOUT]>,
}

impl<K: Num> Digestible for BPlusTreeNonLeaf<K> {
    fn to_digest(&self) -> Digest {
        let children = self
            .children
            .iter()
            .map(|c| c.as_ref().map(|n| n.to_digest()));

        bplus_tree_non_leaf_proof_hash(&self.range, &self.acc_val.to_digest(), children)
    }
}

impl<K: Num> BPlusTreeNonLeaf<K> {
    pub(crate) fn from_hashes(
        range: Range<K>,
        acc_val: AccValue,
        children: SmallVec<[Option<Box<SubProof<K>>>; MAX_INLINE_FANOUT]>,
    ) -> Self {
        Self {
            range,
            acc_val,
            children,
        }
    }
}
