use super::id_tree::IdTreeObjId;
use crate::digest::Digest;

#[inline]
pub(crate) fn id_tree_leaf_hash(obj_id: IdTreeObjId, obj_hash: &Digest) -> Digest {
    todo!(); // concate obj_id and obj_hash
}

#[inline]
pub(crate) fn id_tree_non_leaf_hash<'a>(child_hashes: impl Iterator<Item = &'a Digest>) -> Digest {
    todo!(); // concate_digest_ref
}
