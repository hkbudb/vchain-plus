use serde::{Deserialize, Serialize};

pub mod block;
pub mod block_ads;
pub mod bplus_tree;
pub mod id_tree;
pub mod trie_tree;
pub mod hash;
pub mod object;
pub mod range;
pub mod traits;

pub const MAX_INLINE_FANOUT: usize = 16;

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Parameter {
    pub time_windows: Vec<u64>,
    // pub id_tree_fanout: usize,
    // pub bplus_tree_fanout: usize,
}

#[cfg(test)]
mod tests;
