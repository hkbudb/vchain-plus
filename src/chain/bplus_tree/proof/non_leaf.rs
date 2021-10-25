use crate::digest::Digest;
use crate::{
    chain::{
        bplus_tree::{hash::bplus_tree_non_leaf_proof_hash, proof::sub_proof::SubProof},
        range::Range,
        traits::Num,
        MAX_INLINE_BTREE_FANOUT,
    },
    digest::Digestible,
};
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct BPlusTreeNonLeaf<K: Num> {
    pub(crate) range: Range<K>,
    pub(crate) acc_hash: Digest,
    pub(crate) children: SmallVec<[Option<Box<SubProof<K>>>; MAX_INLINE_BTREE_FANOUT]>,
}

impl<K: Num> Digestible for BPlusTreeNonLeaf<K> {
    fn to_digest(&self) -> Digest {
        let children = self
            .children
            .iter()
            .map(|c| c.as_ref().map(|n| n.to_digest()));

        bplus_tree_non_leaf_proof_hash(&self.range, &self.acc_hash, children)
    }
}

impl<K: Num> BPlusTreeNonLeaf<K> {
    pub(crate) fn from_hashes(
        range: Range<K>,
        acc_hash: Digest,
        children: SmallVec<[Option<Box<SubProof<K>>>; MAX_INLINE_BTREE_FANOUT]>,
    ) -> Self {
        Self {
            range,
            acc_hash,
            children,
        }
    }
}
