use crate::{
    chain::id_tree::{hash::id_tree_leaf_proof_hash, IdTreeNodeId, IdTreeObjId},
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub(crate) struct IdTreeLeaf {
    pub(crate) obj_id: IdTreeObjId,
    pub(crate) node_id: IdTreeNodeId,
    pub(crate) node_hash: Digest,
}

impl Digestible for IdTreeLeaf {
    fn to_digest(&self) -> Digest {
        id_tree_leaf_proof_hash(&self.node_hash)
    }
}

impl IdTreeLeaf {
    pub(crate) fn new(obj_id: IdTreeObjId, node_id: IdTreeNodeId, node_hash: Digest) -> Self {
        Self {
            obj_id,
            node_id,
            node_hash,
        }
    }

    pub(crate) fn value_hash(
        &self,
        obj_id: IdTreeObjId,
        _cur_path_rev: &mut Vec<usize>,
    ) -> Option<Digest> {
        if obj_id == self.obj_id {
            Some(self.node_hash)
        } else {
            Some(Digest::zero())
        }
    }
}
