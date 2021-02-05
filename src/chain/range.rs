use super::types::Num;
use serde::{Deserialize, Serialize};
use std::todo;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct Range<K: Num>(K, K);

impl<K: Num> Range<K> {
    pub fn new(l: K, h: K) -> Self {
        Self(l, h)
    }

    pub fn is_in_range(&self, v: K) -> bool {
        todo!()
    }
}
