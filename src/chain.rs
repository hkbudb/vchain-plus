use serde::{Deserialize, Serialize};

pub mod block;
pub mod block_ads;
pub mod bplus_tree;
pub mod hash;
pub mod id_tree;
pub mod object;
pub mod range;
pub mod traits;
pub mod trie_tree;

const MAX_FANOUT: usize = 16;
const INDEX_NUM: usize = 3;
const INLINE_FANOUT: usize = 8;

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Parameter {
    pub time_windows: Vec<u32>,
}