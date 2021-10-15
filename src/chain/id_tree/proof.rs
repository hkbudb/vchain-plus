use crate::{
    chain::id_tree::{write::fanout_nary_rev, IdTreeNodeId, ObjId},
    digest::{Digest, Digestible},
};
use anyhow::{ensure, Result};
use serde::{Deserialize, Serialize};
use sub_proof::SubProof;

pub(crate) mod leaf;
pub(crate) mod non_leaf;
pub(crate) mod sub_proof;
pub(crate) mod sub_tree;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Proof {
    pub(crate) root: Option<SubProof>,
}

impl Proof {
    pub fn new() -> Self {
        Self::default()
    }

    pub(crate) fn from_subproof(root: SubProof) -> Self {
        Self { root: Some(root) }
    }

    pub fn from_root_hash(root_id: Option<IdTreeNodeId>, root_hash: Digest) -> Self {
        if root_hash == Digest::zero() {
            Self::default()
        } else {
            Self::from_subproof(SubProof::from_hash(root_id, root_hash))
        }
    }

    pub fn root_hash(&self) -> Digest {
        match self.root.as_ref() {
            Some(root) => root.to_digest(),
            None => Digest::zero(),
        }
    }

    fn value_hash(&self, obj_id: ObjId, max_id_num: u16, fanout: u8) -> Digest {
        let depth = (max_id_num as f64).log(fanout as f64).floor() as usize;
        let mut cur_path_rev = fanout_nary_rev(obj_id.to_internal_id().0, fanout, depth);
        match self.root.as_ref() {
            None => Digest::zero(),
            Some(root) => root.value_hash(obj_id.to_internal_id(), &mut cur_path_rev),
        }
    }

    pub fn verify_value(
        &self,
        target_hash: Digest,
        obj_id: ObjId,
        max_id_nun: u16,
        fanout: u8,
    ) -> Result<()> {
        let computed_hash = self.value_hash(obj_id, max_id_nun, fanout);
        ensure!(
            target_hash == computed_hash,
            "Object hash value not matched! The mismatched obj id is {:?}.",
            obj_id,
        );
        Ok(())
    }

    pub(crate) fn remove_node_id(&mut self) {
        if let Some(sub_proof) = &mut self.root {
            sub_proof.remove_node_id();
        }
    }
}
