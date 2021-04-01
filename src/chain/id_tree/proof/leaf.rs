use crate::{
    chain::id_tree::hash::id_tree_leaf_proof_hash,
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub(crate) struct IdTreeLeaf {
    pub(crate) node_hash: Digest, // this is the leaf node hash, not obj_hash
}

impl Digestible for IdTreeLeaf {
    fn to_digest(&self) -> Digest {
        id_tree_leaf_proof_hash(&self.node_hash)
    }
}

impl IdTreeLeaf {
    pub(crate) fn new(node_hash: Digest) -> Self {
        Self { node_hash }
    }
}
