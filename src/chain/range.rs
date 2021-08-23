use crate::{
    chain::{hash::range_hash, traits::Num},
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct Range<K: Num>(K, K);

impl<K: Num> Range<K> {
    pub fn new(l: K, h: K) -> Self {
        Self(l, h)
    }

    pub fn get_low(&self) -> K {
        self.0
    }

    pub fn set_low(&mut self, l: K) {
        self.0 = l;
    }

    pub fn get_high(&self) -> K {
        self.1
    }

    pub fn set_high(&mut self, h: K) {
        self.1 = h;
    }

    pub fn is_in_range(&self, v: K) -> bool {
        self.0 <= v && v <= self.1
    }

    pub fn is_num(&self) -> bool {
        self.0 == self.1
    }

    pub fn can_cover(&self, another: Self) -> bool {
        self.0 <= another.0 && self.1 >= another.1
    }

    pub fn is_covered(&self, another: Self) -> bool {
        another.0 <= self.0 && another.1 >= self.1
    }

    pub fn intersects(&self, another: Self) -> bool {
        self.0 <= another.1 && another.0 <= self.1
    }

    pub fn has_no_intersection(&self, another: Self) -> bool {
        self.1 < another.0 || another.1 < self.0
    }
}

impl<K: Num> Digestible for Range<K> {
    fn to_digest(&self) -> Digest {
        range_hash(self)
    }
}
