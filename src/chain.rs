use crate::acc::{AccPublicKey, AccSecretKey, AccSecretKeyWithPowCache};
use once_cell::sync::Lazy;
use rand::{prelude::*, rngs::StdRng};
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

pub const IDTREE_FANOUT: usize = 3; // to be removed
pub const MAX_FANOUT: usize = 4; // to be removed
pub const MAX_INLINE_FANOUT: usize = 16;

const Q: u64 = 50;
static SEC_KEY: Lazy<AccSecretKeyWithPowCache> = Lazy::new(|| {
    let mut rng = StdRng::seed_from_u64(123_456_789u64);
    let sk = AccSecretKey::rand(&mut rng);
    sk.into()
});
static PUB_KEY: Lazy<AccPublicKey> = Lazy::new(|| AccPublicKey::gen_key(&(*SEC_KEY), Q));

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Parameter {
    pub time_windows: Vec<u64>,
    // pub id_tree_fanout: usize,
    // pub bplus_tree_fanout: usize,
}
