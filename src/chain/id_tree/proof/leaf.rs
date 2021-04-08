use crate::{
    chain::id_tree::{hash::id_tree_leaf_proof_hash, IdTreeObjId},
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub(crate) struct IdTreeLeaf {
    pub(crate) obj_id: IdTreeObjId,
    pub(crate) node_hash: Digest, // this is the leaf node hash, not obj_hash
}

impl Digestible for IdTreeLeaf {
    fn to_digest(&self) -> Digest {
        id_tree_leaf_proof_hash(&self.node_hash)
    }
}

impl IdTreeLeaf {
    pub(crate) fn new(obj_id: IdTreeObjId, node_hash: Digest) -> Self {
        Self { obj_id, node_hash }
    }

    pub(crate) fn value_hash(
        &self,
        obj_id: IdTreeObjId,
        cur_path_rev: &mut Vec<usize>,
    ) -> Option<Digest> {
        if obj_id == self.obj_id {
            Some(self.node_hash)
        } else {
            Some(Digest::zero())
        }
    }
}
