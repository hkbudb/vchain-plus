use crate::{
    chain::{block::Height, hash::object_hash, traits::Num},
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct Object<K: Num> {
    pub blk_height: Height,
    pub num_data: Vec<K>,
    pub keyword_data: HashSet<String>,
}

impl<K: Num> Object<K> {
    pub fn new(blk_height: Height, num_data: Vec<K>, keyword_data: HashSet<String>) -> Self {
        Self {
            blk_height,
            num_data,
            keyword_data,
        }
    }
}

impl<K: Num> Digestible for Object<K> {
    fn to_digest(&self) -> Digest {
        object_hash(self.blk_height, &self.num_data, &self.keyword_data)
    }
}
