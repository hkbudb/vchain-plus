use crate::{
    chain::{range::Range, traits::Num},
    digest::{blake2, concat_digest_ref, Digest, Digestible},
};

#[inline]
pub(crate) fn bplus_tree_leaf_hash<K: Num>(num: K, acc_hash: &Digest) -> Digest {
    let mut state = blake2().to_state();
    state.update(num.to_digest().as_bytes());
    state.update(acc_hash.as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn bplus_tree_leaf_proof_hash<K: Num>(num: &K, acc_hash: &Digest) -> Digest {
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

#[inline]
pub(crate) fn bplus_tree_non_leaf_proof_hash<K: Num>(
    range: &Range<K>,
    acc_hash: &Digest,
    children: impl Iterator<Item = Option<Digest>>,
) -> Digest {
    let mut has_child = false;
    let mut state = blake2().to_state();
    state.update(range.to_digest().as_bytes());
    state.update(acc_hash.as_bytes());

    let mut state2 = blake2().to_state();
    for child in children {
        let child_hash = match child {
            Some(d) => d,
            None => Digest::zero(),
        };
        has_child = has_child || (!child_hash.is_zero());
        state2.update(child_hash.as_bytes());
    }
    let sub_hash = Digest::from(state2.finalize());

    state.update(sub_hash.as_bytes());
    if !has_child {
        return Digest::zero();
    }
    Digest::from(state.finalize())
}
