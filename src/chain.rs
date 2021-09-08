use serde::{Deserialize, Serialize};

pub mod block;
pub mod bplus_tree;
pub mod hash;
pub mod id_tree;
pub mod object;
pub mod query;
pub mod range;
pub mod traits;
pub mod trie_tree;
pub mod verify;

pub const ID_FANOUT: usize = 2;
pub const MAX_INLINE_FANOUT: usize = 4;
pub const COST_COEFFICIENT: usize = 50;

#[derive(Debug, Default, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Parameter {
    pub time_win_sizes: Vec<u64>,
    pub id_tree_fanout: usize,
    pub max_id_num: usize,
    pub bplus_tree_fanout: usize,
    pub num_dim: usize,
}

#[cfg(test)]
mod tests;
