use crate::{
    chain::{block::Height, range::Range, traits::Num},
    digest::{blake2, concat_digest, Digest, Digestible},
};
use std::collections::HashSet;

#[inline]
pub(crate) fn range_hash<K: Num>(range: &Range<K>) -> Digest {
    let mut state = blake2().to_state();
    state.update(range.get_low().to_digest().as_bytes());
    state.update(range.get_high().to_digest().as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn object_hash<K: Num>(
    blk_height: Height,
    num_data: &[K],
    keyword_data: &HashSet<String>,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(&blk_height.to_le_bytes());

    let num_hash = concat_digest(num_data.iter().map(|n| n.to_digest()));
    state.update(&num_hash.0);

    let mut keywords: Vec<_> = keyword_data.iter().collect();
    keywords.sort_unstable();
    let keyword_hash = concat_digest(keywords.iter().map(|w| w.to_digest()));
    state.update(&keyword_hash.0);

    Digest::from(state.finalize())
}
