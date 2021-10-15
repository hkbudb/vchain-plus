use crate::{chain::id_tree::IdTreeNodeId, digest::Digest};
use serde::{Deserialize, Serialize};

#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub(crate) struct IdTreeSubTree {
    pub(crate) node_id: Option<IdTreeNodeId>,
    pub(crate) node_hash: Digest,
}

impl IdTreeSubTree {
    pub(crate) fn new(node_id: Option<IdTreeNodeId>, node_hash: Digest) -> Self {
        Self { node_id, node_hash }
    }
    pub(crate) fn get_node_hash(&self) -> Digest {
        self.node_hash
    }
}
