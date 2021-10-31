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

pub const MAX_ININE_ID_FANOUT: usize = 32;
pub const MAX_INLINE_BTREE_FANOUT: usize = 32;
pub const COST_COEFFICIENT: usize = 200;

#[derive(Debug, Default, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Parameter {
    pub time_win_sizes: Vec<u16>,
    pub id_tree_fanout: u8,
    pub max_id_num: u16,
    pub bplus_tree_fanout: u8,
    pub num_dim: u8,
}

#[cfg(test)]
pub(crate) mod tests;
