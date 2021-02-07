use super::{block::BlockId, id_tree::IdTreeObjId, object::ObjId, range::Range, traits::Num};
use crate::{
    acc::acc_values::AccValue,
    digest::{blake2, concat_digest_ref, Digest, Digestible},
};
use ark_ec::PairingEngine;
use std::collections::HashSet;

#[inline]
pub(crate) fn range_hash<K: Num>(range: &Range<K>) -> Digest {
    let mut state = blake2().to_state();
    state.update(&range.get_low().to_digest().0);
    state.update(&range.get_high().to_digest().0);
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn id_tree_leaf_hash(obj_id: IdTreeObjId, obj_hash: &Digest) -> Digest {
    let mut state = blake2().to_state();
    state.update(&obj_id.to_le_bytes());
    state.update(&obj_hash.0);
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn id_tree_non_leaf_hash<'a>(child_hashes: impl Iterator<Item = &'a Digest>) -> Digest {
    concat_digest_ref(child_hashes)
}

#[inline]
pub(crate) fn bplus_tree_leaf_hash<K: Num, E: PairingEngine>(
    num: &K,
    data_set_acc: &AccValue<E>,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(&num.to_digest().0);
    //state.update(&data_set_acc.to_digest());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn bplus_tree_non_leaf_hash<'a, K: Num, E: PairingEngine>(
    range: &Range<K>,
    data_set_acc: &AccValue<E>,
    child_hashes: impl Iterator<Item = &'a Digest>,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(&range.to_digest().0);
    //state.update(&data_set_acc.to_digest());
    state.update(&concat_digest_ref(child_hashes).0);
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn trie_leaf_hash<E: PairingEngine>(
    keyword: &String,
    data_set_acc: &AccValue<E>,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(keyword.as_bytes());
    //state.update(&data_set_acc.to_digest());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn trie_non_leaf_hash<'a, E: PairingEngine>(
    keyword_pre: &String,
    data_set_acc: &AccValue<E>,
    child_hashes: impl Iterator<Item = &'a Digest>,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(keyword_pre.as_bytes());
    //state.update(&data_set_acc.to_digest());
    state.update(&concat_digest_ref(child_hashes).0);
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn block_header_hash<'a, E: PairingEngine>(
    block_id: BlockId,
    prev_hash: &Digest,
    id_root_dig: &Digest,
    ads_root_dig: impl Iterator<Item = &'a Digest>,
    data_set_acc: &AccValue<E>,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(&block_id.to_le_bytes());
    state.update(&prev_hash.0);
    state.update(&id_root_dig.0);
    state.update(&concat_digest_ref(ads_root_dig).0);
    //state.update(&data_set_acc.to_digest());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn object_hash<'a, K: Num>(
    id: ObjId,
    block_id: BlockId,
    //num_data: impl Iterator<Item = &'a K>,
    keyword_data: impl Iterator<Item = &'a HashSet<String>>,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(&block_id.to_le_bytes());
    // todo
    Digest::from(state.finalize())
}
