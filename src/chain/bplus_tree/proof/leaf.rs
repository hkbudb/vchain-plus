use super::super::hash::bplus_tree_leaf_proof_hash;
use crate::{
    acc::AccValue,
    chain::traits::Num,
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct BPlusTreeLeaf<K: Num> {
    pub(crate) num: K,
    pub(crate) acc_val: AccValue,
}

impl<K: Num> Digestible for BPlusTreeLeaf<K> {
    fn to_digest(&self) -> Digest {
        bplus_tree_leaf_proof_hash(&self.num, &self.acc_val.to_digest())
    }
}

impl<K: Num> BPlusTreeLeaf<K> {
    pub(crate) fn new(num: K, acc_val: AccValue) -> Self {
        Self { num, acc_val }
    }

    // pub(crate) fn value_hash(&self, range: Range<K>) -> Option<AccValue> {
    //     if range.is_in_range(self.num) {
    //         Some(self.acc_hash)
    //     } else {
    //         None
    //     }
    // }
}
