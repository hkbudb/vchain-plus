use super::{block::BlockId, hash::object_hash, traits::Num};
use crate::{
    create_id_type,
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;

create_id_type!(ObjId);
#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct Object<K: Num> {
    pub id: ObjId,
    pub block_id: BlockId,
    pub num_data: Vec<K>,
    pub keyword_data: HashSet<String>, // HashSet: automically remove duplicates
}

impl<K: Num> Object<K> {
    pub fn new(block_id: BlockId, num_data: Vec<K>, keyword_data: HashSet<String>) -> Self {
        Self {
            id: ObjId::next_id(),
            block_id,
            num_data,
            keyword_data,
        }
    }

    pub fn new_dbg(
        id: ObjId,
        block_id: BlockId,
        num_data: Vec<K>,
        keyword_data: HashSet<String>,
    ) -> Self {
        Self {
            id,
            block_id,
            num_data,
            keyword_data,
        }
    }
}

impl<K: Num> Digestible for Object<K> {
    fn to_digest(&self) -> Digest {
        object_hash(self.id, self.block_id, &self.num_data, &self.keyword_data)
    }
}
