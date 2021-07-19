use crate::{
    acc::{AccPublicKey, AccValue},
    chain::{range::Range, traits::Num},
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};
use sub_proof::SubProof;
pub(crate) mod leaf;
pub(crate) mod non_leaf;
pub(crate) mod res_sub_tree;
pub(crate) mod sub_proof;
pub(crate) mod sub_tree;
use anyhow::{anyhow, bail, Result};

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Proof<K: Num> {
    pub(crate) root: Option<SubProof<K>>,
}

impl<K: Num> Proof<K> {
    pub(crate) fn from_subproof(root: SubProof<K>) -> Self {
        Self { root: Some(root) }
    }

    pub(crate) fn root_hash(&self) -> Digest {
        match self.root.as_ref() {
            Some(root) => root.to_digest(),
            None => Digest::zero(),
        }
    }

    pub(crate) fn verify(
        &self,
        query_range: Range<K>,
        acc_val: AccValue,
        pk: &AccPublicKey,
    ) -> Result<Digest> {
        if self
            .root
            .as_ref()
            .ok_or_else(|| anyhow!("Cannot find subproof!"))?
            .value_acc_completeness(query_range, pk)?
            != acc_val
        {
            bail!("B plus tree verification: acc value not matched");
        }
        Ok(self.root_hash())
    }
}
