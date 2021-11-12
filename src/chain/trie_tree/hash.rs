use crate::{
    chain::trie_tree::{proof::sub_proof::SubProof, TrieNodeId},
    digest::{blake2, Digest, Digestible},
};

#[inline]
pub(crate) fn trie_leaf_hash(rest_hash: &Digest, acc_hash: &Digest) -> Digest {
    let mut state = blake2().to_state();
    state.update(rest_hash.as_bytes());
    state.update(acc_hash.as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn trie_leaf_proof_hash(rest_hash: &Digest, acc_hash: &Digest) -> Digest {
    let mut state = blake2().to_state();
    state.update(rest_hash.as_bytes());
    state.update(acc_hash.as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn trie_non_leaf_node_hash<'a>(
    nibble_hash: &Digest,
    child_hashes: impl Iterator<Item = (&'a char, &'a (TrieNodeId, Digest))>,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(nibble_hash.as_bytes());

    let mut state2 = blake2().to_state();
    for (char, (_id, hash)) in child_hashes {
        state2.update(char.to_string().to_digest().as_bytes());
        state2.update(hash.as_bytes());
    }
    let sub_hash = Digest::from(state2.finalize());

    state.update(sub_hash.as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn trie_non_leaf_root_hash<'a>(
    nibble_hash: &Digest,
    acc_hash: &Digest,
    child_hashes: impl Iterator<Item = (&'a char, &'a (TrieNodeId, Digest))>,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(nibble_hash.as_bytes());
    state.update(acc_hash.as_bytes());

    let mut state2 = blake2().to_state();
    for (char, (_id, hash)) in child_hashes {
        state2.update(char.to_string().to_digest().as_bytes());
        state2.update(hash.as_bytes());
    }
    let sub_hash = Digest::from(state2.finalize());

    state.update(sub_hash.as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn trie_non_leaf_proof_hash<'a>(
    nibble_hash: &Digest,
    children: impl Iterator<Item = (&'a char, &'a Box<SubProof>)>,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(nibble_hash.as_bytes());

    let mut state2 = blake2().to_state();
    for (char, sub_proof) in children {
        state2.update(char.to_string().to_digest().as_bytes());
        state2.update(sub_proof.as_ref().to_digest().as_bytes());
    }
    let sub_hash = Digest::from(state2.finalize());

    state.update(sub_hash.as_bytes());
    Digest::from(state.finalize())
}

#[inline]
pub(crate) fn trie_non_leaf_root_proof_hash<'a>(
    nibble_hash: &Digest,
    acc_hash: &Digest,
    children: impl Iterator<Item = (&'a char, &'a Box<SubProof>)>,
) -> Digest {
    let mut state = blake2().to_state();
    state.update(nibble_hash.as_bytes());
    state.update(acc_hash.as_bytes());

    let mut state2 = blake2().to_state();
    for (char, sub_proof) in children {
        state2.update(char.to_string().to_digest().as_bytes());
        state2.update(sub_proof.as_ref().to_digest().as_bytes());
    }
    let sub_hash = Digest::from(state2.finalize());

    state.update(sub_hash.as_bytes());
    Digest::from(state.finalize())
}
