use std::num::NonZeroU16;

use crate::{
    chain::{
        block::{block_ads::BlockADS, Height},
        bplus_tree::BPlusTreeRoot,
        trie_tree::TrieRoot,
    },
    digest::{blake2, concat_digest_ref, Digest, Digestible},
};

#[inline]
pub(crate) fn block_head_hash(
    blk_height: Height,
    prev_hash: &Digest,
    ads_hash: &Digest,
    obj_root_hash: &Digest,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(&blk_height.to_le_bytes());
    state.update(prev_hash.as_bytes());
    state.update(ads_hash.as_bytes());
    state.update(obj_root_hash.as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn block_ads_hash<'a>(
    bplus_roots: impl Iterator<Item = &'a BPlusTreeRoot>,
    trie_root: &TrieRoot,
) -> Digest {
    let mut state = blake2().to_state();
    for bplus_root in bplus_roots {
        state.update(bplus_root.to_digest().as_bytes());
    }
    let bplus_hash = Digest::from(state.finalize());
    let mut state = blake2().to_state();
    state.update(bplus_hash.as_bytes());
    state.update(trie_root.to_digest().as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn block_multi_ads_hash<'a>(
    block_adses: impl Iterator<Item = (&'a u16, &'a BlockADS)>,
) -> Digest {
    let mut state = blake2().to_state();
    for (window_siz, blk_ads) in block_adses {
        state.update(window_siz.to_digest().as_bytes());
        state.update(blk_ads.to_digest().as_bytes());
    }
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn obj_id_nums_hash<'a>(obj_id_nums: impl Iterator<Item = &'a NonZeroU16>) -> Digest {
    let mut state = blake2().to_state();
    for obj_id_num in obj_id_nums {
        state.update(obj_id_num.get().to_digest().as_bytes());
    }
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn obj_root_hash<'a>(obj_hashes: impl Iterator<Item = &'a Digest>) -> Digest {
    let mut state = blake2().to_state();
    state.update(concat_digest_ref(obj_hashes).as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn ads_root_hash(
    id_set_root_hash: &Digest,
    id_tree_root_hash: &Digest,
    ads_hash: &Digest,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(id_set_root_hash.as_bytes());
    state.update(id_tree_root_hash.as_bytes());
    state.update(ads_hash.as_bytes());
    Digest::from(state.finalize())
}
