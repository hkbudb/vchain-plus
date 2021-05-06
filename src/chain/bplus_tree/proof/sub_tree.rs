use crate::{
    chain::{range::Range, traits::Num},
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct BPlusTreeSubTree<K: Num> {
    pub(crate) range: Range<K>,
    pub(crate) node_hash: Digest,
}

impl<K: Num> Digestible for BPlusTreeSubTree<K> {
    fn to_digest(&self) -> Digest {
        self.node_hash
    }
}

impl<K: Num> BPlusTreeSubTree<K> {
    pub(crate) fn new(range: Range<K>, node_hash: Digest) -> Self {
        Self { range, node_hash }
    }
}
