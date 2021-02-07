use super::{hash::range_hash, traits::Num};
use crate::digest::{Digest, Digestible};
use serde::{Deserialize, Serialize};
/// range is [l, h)
#[derive(Debug, Copy, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct Range<K: Num>(K, K);

impl<K: Num> Range<K> {
    pub fn new(l: K, h: K) -> Self {
        Self(l, h)
    }

    pub fn get_low(&self) -> K {
        self.0
    }

    pub fn get_high(&self) -> K {
        self.1
    }

    pub fn is_in_range(&self, v: K) -> bool {
        self.0 <= v && v < self.1
    }
}

impl<K: Num> Digestible for Range<K> {
    fn to_digest(&self) -> Digest {
        range_hash(&self)
    }
}
