use crate::digest::{Digest, Digestible, blake2, concat_digest_ref};
use super::super::{traits::Num, range::Range};

#[inline]
pub(crate) fn bplus_tree_leaf_hash<K: Num>(num: K, acc_hash: &Digest) -> Digest {
    let mut state = blake2().to_state();
    state.update(num.to_digest().as_bytes());
    state.update(acc_hash.as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn bplus_tree_non_leaf_hash<'a, K: Num>(
    range: &Range<K>,
    acc_hash: &Digest,
    child_hashes: impl Iterator<Item = &'a Digest>,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(range.to_digest().as_bytes());
    state.update(acc_hash.as_bytes());
    state.update(concat_digest_ref(child_hashes).as_bytes());
    Digest::from(state.finalize())
}
