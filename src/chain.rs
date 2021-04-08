use serde::{Deserialize, Serialize};

pub mod block;
pub mod block_ads;
pub mod bplus_tree;
pub mod id_tree;
pub mod trie_tree;

pub mod hash;
pub mod tests;

pub mod object;
pub mod range;
pub mod traits;

pub const IDTREE_FANOUT: usize = 3;
pub const MAX_FANOUT: usize = 16; // 3 2
                                  //const INDEX_NUM: usize = 3;
                                  //const INLINE_FANOUT: usize = 8;

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Parameter {
    pub time_windows: Vec<u64>,
}
