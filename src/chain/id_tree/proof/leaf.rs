use crate::{
    chain::id_tree::{hash::id_tree_leaf_proof_hash, IdTreeInternalId, IdTreeNodeId},
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub(crate) struct IdTreeLeaf {
    pub(crate) obj_id: IdTreeInternalId,
    pub(crate) node_id: Option<IdTreeNodeId>,
    pub(crate) node_hash: Digest,
}

impl Digestible for IdTreeLeaf {
    fn to_digest(&self) -> Digest {
        id_tree_leaf_proof_hash(&self.node_hash)
    }
}

impl IdTreeLeaf {
    pub(crate) fn new(
        obj_id: IdTreeInternalId,
        node_id: Option<IdTreeNodeId>,
        node_hash: Digest,
    ) -> Self {
        Self {
            obj_id,
            node_id,
            node_hash,
        }
    }

    pub(crate) fn value_hash(
        &self,
        obj_id: IdTreeInternalId,
        _cur_path_rev: &mut [usize],
    ) -> Digest {
        if obj_id == self.obj_id {
            self.node_hash
        } else {
            Digest::zero()
        }
    }
}
