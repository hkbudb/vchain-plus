use crate::{
    chain::id_tree::IdTreeInternalId,
    digest::{blake2, concat_digest_ref, Digest},
};

#[inline]
pub(crate) fn id_tree_leaf_hash(obj_id: IdTreeInternalId, obj_hash: &Digest) -> Digest {
    let mut state = blake2().to_state();
    state.update(&obj_id.to_le_bytes());
    state.update(obj_hash.as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn id_tree_non_leaf_hash<'a>(child_hashes: impl Iterator<Item = &'a Digest>) -> Digest {
    concat_digest_ref(child_hashes)
}

#[inline]
pub(crate) fn id_tree_leaf_proof_hash(node_hash: &Digest) -> Digest {
    *node_hash
}

#[inline]
pub(crate) fn id_tree_non_leaf_proof_hash(
    children: impl Iterator<Item = Option<Digest>>,
) -> Digest {
    let mut has_child = false;
    let mut state = blake2().to_state();

    for child in children {
        let child_hash = match child {
            Some(d) => d,
            None => Digest::zero(),
        };
        has_child = has_child || (!child_hash.is_zero());
        state.update(child_hash.as_bytes());
    }

    if !has_child {
        return Digest::zero();
    }
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn id_tree_root_hash(cur_obj_id_hash: &Digest, id_tree_root_hash: &Digest) -> Digest {
    let mut state = blake2().to_state();
    state.update(cur_obj_id_hash.as_bytes());
    state.update(id_tree_root_hash.as_bytes());
    Digest::from(state.finalize())
}
