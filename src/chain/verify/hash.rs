use crate::{
    chain::{id_tree::ObjId, object::Object, traits::Num},
    digest::{blake2, Digest, Digestible},
};

#[inline]
pub(crate) fn merkle_proof_hash<'a>(
    id_set_root_hash: &Digest,
    id_tree_root_hash: &Digest,
    block_ads_hashes: impl Iterator<Item = (&'a u16, &'a Digest)>,
) -> Digest {
    let mut state = blake2().to_state();
    for (window_siz, blk_ads_hash) in block_ads_hashes {
        state.update(window_siz.to_digest().as_bytes());
        state.update(blk_ads_hash.as_bytes());
    }
    let ads_hash = Digest::from(state.finalize());
    let mut state = blake2().to_state();
    state.update(id_set_root_hash.as_bytes());
    state.update(id_tree_root_hash.as_bytes());
    state.update(ads_hash.as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn bplus_roots_hash<'a>(hashes: impl Iterator<Item = (&'a u8, &'a Digest)>) -> Digest {
    let mut state = blake2().to_state();
    for (_dim, hash) in hashes {
        state.update(hash.as_bytes());
    }
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn ads_hash(bplus_hash: Digest, trie_hash: Digest) -> Digest {
    let mut state = blake2().to_state();
    state.update(bplus_hash.as_bytes());
    state.update(trie_hash.as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn obj_hash<K: Num>(obj: &Object<K>, id: &ObjId) -> Digest {
    let mut state = blake2().to_state();
    state.update(&id.to_internal_id().to_le_bytes());
    state.update(obj.to_digest().as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn id_tree_root_hash(cur_obj_id_hash: Digest, id_tree_root_node_hash: Digest) -> Digest {
    let mut state = blake2().to_state();
    state.update(cur_obj_id_hash.as_bytes());
    state.update(id_tree_root_node_hash.as_bytes());
    Digest::from(state.finalize())
}
