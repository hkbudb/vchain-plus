use super::{block::BlockId, /*id_tree::IdTreeObjId, */ object::ObjId, range::Range, traits::Num,};
use crate::digest::{blake2, concat_digest, /*concat_digest_ref,*/ Digest, Digestible};
use std::collections::HashSet;

#[inline]
pub(crate) fn range_hash<K: Num>(range: &Range<K>) -> Digest {
    let mut state = blake2().to_state();
    state.update(range.get_low().to_digest().as_bytes());
    state.update(range.get_high().to_digest().as_bytes());
    Digest::from(state.finalize())
}

// #[inline]
// pub(crate) fn bplus_tree_leaf_hash<K: Num>(num: K, acc_hash: &Digest) -> Digest {
//     let mut state = blake2().to_state();
//     state.update(num.to_digest().as_bytes());
//     state.update(acc_hash.as_bytes());
//     Digest::from(state.finalize())
// }

// #[inline]
// pub(crate) fn bplus_tree_non_leaf_hash<'a, K: Num>(
//     range: &Range<K>,
//     acc_hash: &Digest,
//     child_hashes: impl Iterator<Item = &'a Digest>,
// ) -> Digest {
//     let mut state = blake2().to_state();
//     state.update(range.to_digest().as_bytes());
//     state.update(acc_hash.as_bytes());
//     state.update(concat_digest_ref(child_hashes).as_bytes());
//     Digest::from(state.finalize())
// }

// #[inline]
// pub(crate) fn trie_leaf_hash(acc_hash: Digest) -> Digest {
//     acc_hash
// }

// #[inline]
// pub(crate) fn trie_non_leaf_hash<'a>(
//     nibble: &str,
//     acc_hash: &Digest,
//     child_hashes: impl Iterator<Item = &'a Digest>,
// ) -> Digest {
//     let mut state = blake2().to_state();
//     state.update(nibble.to_digest().as_bytes());
//     state.update(acc_hash.as_bytes());
//     state.update(concat_digest_ref(child_hashes).as_bytes());
//     Digest::from(state.finalize())
// }

#[inline]
pub(crate) fn block_head_hash<'a>(
    block_id: BlockId,
    prev_hash: &Digest,
    id_tree_root_hash: &Digest,
    ads_hash: &Digest,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(&block_id.to_le_bytes());
    state.update(prev_hash.as_bytes());
    state.update(&id_tree_root_hash.as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn object_hash<K: Num>(
    id: ObjId,
    block_id: BlockId,
    num_data: &[K],
    keyword_data: &HashSet<String>,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(&id.to_le_bytes());
    state.update(&block_id.to_le_bytes());

    let num_hash = concat_digest(num_data.iter().map(|n| n.to_digest()));
    state.update(&num_hash.0);

    let mut keywords: Vec<_> = keyword_data.iter().collect();
    keywords.sort_unstable();
    let keyword_hash = concat_digest(keywords.iter().map(|w| w.to_digest()));
    state.update(&keyword_hash.0);

    Digest::from(state.finalize())
}
