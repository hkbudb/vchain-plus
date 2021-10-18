use crate::digest::Digestible;
use crate::{
    chain::{
        block::hash::{block_ads_hash, block_multi_ads_hash},
        bplus_tree::BPlusTreeRoot,
        trie_tree::TrieRoot,
    },
    digest::Digest,
};
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

#[derive(Debug, Clone, Eq, PartialEq, Default, Serialize, Deserialize)]
pub struct BlockADS {
    pub bplus_tree_roots: Vec<BPlusTreeRoot>,
    pub trie_root: TrieRoot,
}

impl Digestible for BlockADS {
    fn to_digest(&self) -> Digest {
        block_ads_hash(self.bplus_tree_roots.iter(), &self.trie_root)
    }
}

impl BlockADS {
    fn set_trie_root(&mut self, trie_root: TrieRoot) {
        self.trie_root = trie_root;
    }

    fn set_bplus_roots(&mut self, bplus_roots: Vec<BPlusTreeRoot>) {
        self.bplus_tree_roots = bplus_roots;
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Default, Serialize, Deserialize)]
pub struct BlockMultiADS(BTreeMap<u16, BlockADS>);

impl Digestible for BlockMultiADS {
    fn to_digest(&self) -> Digest {
        block_multi_ads_hash(self.0.iter())
    }
}

impl BlockMultiADS {
    pub(crate) fn read_adses(&self) -> &BTreeMap<u16, BlockADS> {
        &self.0
    }

    pub(crate) fn read_bplus_root(&self, time_win: u16, dim: u8) -> Result<BPlusTreeRoot> {
        let blk_ads = self.0.get(&time_win);
        let ads =
            blk_ads.with_context(|| format!("Cannot find the ADS in time window {}", time_win))?;
        Ok(*ads
            .bplus_tree_roots
            .get(dim as usize)
            .with_context(|| format!("Cannot find the bplus tree root at dimension {}", dim))?)
    }

    pub(crate) fn read_trie_root(&self, time_win: u16) -> Result<TrieRoot> {
        let blk_ads = self.0.get(&time_win);
        Ok(blk_ads
            .with_context(|| format!("Cannot find trie root in time window {}", time_win))?
            .trie_root)
    }

    pub(crate) fn set_multi_trie_roots<'a>(
        &mut self,
        trie_roots: impl Iterator<Item = &'a (u16, TrieRoot)>,
    ) {
        for (k, trie_root) in trie_roots {
            if let Some(blk_ads) = self.0.get_mut(k) {
                blk_ads.set_trie_root(*trie_root);
            } else {
                let mut new_blk_ads = BlockADS::default();
                new_blk_ads.set_trie_root(*trie_root);
                self.0.insert(*k, new_blk_ads);
            }
        }
    }

    pub(crate) fn set_multi_bplus_roots<'a>(
        &mut self,
        bplus_roots: impl Iterator<Item = &'a (u16, Vec<BPlusTreeRoot>)>,
    ) {
        for (k, vec) in bplus_roots {
            if let Some(blk_ads) = self.0.get_mut(k) {
                blk_ads.set_bplus_roots(vec.clone());
            }
        }
    }
}
