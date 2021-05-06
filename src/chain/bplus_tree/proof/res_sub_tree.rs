use crate::{
    acc::AccValue,
    chain::{range::Range, traits::Num},
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct BPlusTreeResSubTree<K: Num> {
    pub(crate) range: Range<K>,
    pub(crate) acc_val: AccValue,
    pub(crate) node_hash: Digest,
}

impl<K: Num> Digestible for BPlusTreeResSubTree<K> {
    fn to_digest(&self) -> Digest {
        self.node_hash
    }
}

impl<K: Num> BPlusTreeResSubTree<K> {
    pub(crate) fn new(range: Range<K>, acc_val: AccValue, node_hash: Digest) -> Self {
        Self {
            range,
            acc_val,
            node_hash,
        }
    }
}
