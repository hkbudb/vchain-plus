pub mod block;
pub mod bplus_tree;
pub mod hash;
pub mod id_tree;
pub mod object;
pub mod range;
pub mod traits;
pub mod trie_tree;

const MAX_FANOUT: usize = 16;
const INDEX_NUM: usize = 3;
