#![cfg_attr(not(test), warn(clippy::unwrap_used))]

#[macro_use]
extern crate tracing;

pub mod acc;
pub mod chain;
pub mod digest;
pub mod utils;

use anyhow::{Context, Result};
use chain::{
    block::{BlockContent, BlockHead, Height},
    bplus_tree::{BPlusTreeNode, BPlusTreeNodeId},
    id_tree::{IdTreeNode, IdTreeNodeId},
    object::Object,
    range::Range,
    traits::{ReadInterface, ScanQueryInterface, WriteInterface},
    trie_tree::{TrieNode, TrieNodeId},
    Parameter,
};
use digest::{Digest, Digestible};
use rocksdb::{self, DB};
use std::{
    collections::HashSet,
    fs,
    path::{Path, PathBuf},
};

pub struct SimChain {
    root_path: PathBuf,
    param: Parameter,
    block_head_db: DB,
    block_content_db: DB,
    id_tree_db: DB,
    bplus_tree_db: DB,
    trie_db: DB,
    obj_db: DB,
}

impl SimChain {
    pub fn create(path: &Path, param: Parameter) -> Result<Self> {
        fs::create_dir_all(path).with_context(|| format!("failed to create dir {:?}", path))?;
        fs::write(
            path.join("param.json"),
            serde_json::to_string_pretty(&param)?,
        )?;
        let mut opts = rocksdb::Options::default();
        opts.create_if_missing(true);
        Ok(Self {
            root_path: path.to_owned(),
            param,
            block_head_db: DB::open(&opts, path.join("blk_head.db"))?,
            block_content_db: DB::open(&opts, path.join("block_content.db"))?,
            id_tree_db: DB::open(&opts, path.join("id_tree.db"))?,
            bplus_tree_db: DB::open(&opts, path.join("bplus_tree.db"))?,
            trie_db: DB::open(&opts, path.join("trie.db"))?,
            obj_db: DB::open(&opts, path.join("obj.db"))?,
        })
    }

    pub fn open(path: &Path) -> Result<Self> {
        Ok(Self {
            root_path: path.to_owned(),
            param: serde_json::from_str::<Parameter>(&fs::read_to_string(
                path.join("param.json"),
            )?)?,
            block_head_db: DB::open_default(path.join("blk_head.db"))?,
            block_content_db: DB::open_default(path.join("block_content.db"))?,
            id_tree_db: DB::open_default(path.join("id_tree.db"))?,
            bplus_tree_db: DB::open_default(path.join("bplus_tree.db"))?,
            trie_db: DB::open_default(path.join("trie.db"))?,
            obj_db: DB::open_default(path.join("obj.db"))?,
        })
    }
}

impl ReadInterface for &SimChain {
    type K = u32;
    fn get_parameter(&self) -> Result<Parameter> {
        Ok(self.param.clone())
    }
    fn read_block_head(&self, blk_heihgt: Height) -> Result<BlockHead> {
        let data = self
            .block_head_db
            .get(blk_heihgt.to_le_bytes())?
            .context("failed to read block head")?;
        Ok(bincode::deserialize::<BlockHead>(&data[..])?)
    }
    fn read_block_content(&self, blk_height: Height) -> Result<BlockContent> {
        let data = self
            .block_content_db
            .get(blk_height.to_le_bytes())?
            .context("failed to read block content")?;
        Ok(bincode::deserialize::<BlockContent>(&data[..])?)
    }
    fn read_id_tree_node(&self, id_tree_node_id: IdTreeNodeId) -> Result<IdTreeNode> {
        let data = self
            .id_tree_db
            .get(id_tree_node_id.to_le_bytes())?
            .context("failed to read id tree node")?;
        Ok(bincode::deserialize::<IdTreeNode>(&data[..])?)
    }
    fn read_bplus_tree_node(
        &self,
        bplus_tree_node_id: BPlusTreeNodeId,
    ) -> Result<BPlusTreeNode<Self::K>> {
        let data = self
            .bplus_tree_db
            .get(bplus_tree_node_id.to_le_bytes())?
            .with_context(|| {
                format!(
                    "failed to read bplus tree node with id {:?}",
                    bplus_tree_node_id
                )
            })?;
        Ok(bincode::deserialize::<BPlusTreeNode<Self::K>>(&data[..])?)
    }
    fn read_trie_node(&self, trie_node_id: TrieNodeId) -> Result<TrieNode> {
        let data = self
            .trie_db
            .get(trie_node_id.to_le_bytes())?
            .context("failed to read trie node")?;
        Ok(bincode::deserialize::<TrieNode>(&data[..])?)
    }
    fn read_object(&self, obj_hash: Digest) -> Result<Object<Self::K>> {
        let data = self
            .obj_db
            .get(obj_hash.as_bytes())?
            .context("failed to read object")?;
        Ok(bincode::deserialize::<Object<Self::K>>(&data[..])?)
    }
}

impl ReadInterface for &mut SimChain {
    type K = u32;
    fn get_parameter(&self) -> Result<Parameter> {
        Ok(self.param.clone())
    }
    fn read_block_head(&self, blk_heihgt: Height) -> Result<BlockHead> {
        let data = self
            .block_head_db
            .get(blk_heihgt.to_le_bytes())?
            .context("failed to read block head")?;
        Ok(bincode::deserialize::<BlockHead>(&data[..])?)
    }
    fn read_block_content(&self, blk_height: Height) -> Result<BlockContent> {
        let data = self
            .block_content_db
            .get(blk_height.to_le_bytes())?
            .context("failed to read block content")?;
        Ok(bincode::deserialize::<BlockContent>(&data[..])?)
    }
    fn read_id_tree_node(&self, id_tree_node_id: IdTreeNodeId) -> Result<IdTreeNode> {
        let data = self
            .id_tree_db
            .get(id_tree_node_id.to_le_bytes())?
            .context("failed to read id tree node")?;
        Ok(bincode::deserialize::<IdTreeNode>(&data[..])?)
    }
    fn read_bplus_tree_node(
        &self,
        bplus_tree_node_id: BPlusTreeNodeId,
    ) -> Result<BPlusTreeNode<Self::K>> {
        let data = self
            .bplus_tree_db
            .get(bplus_tree_node_id.to_le_bytes())?
            .with_context(|| {
                format!(
                    "failed to read bplus tree node with id {:?}",
                    bplus_tree_node_id
                )
            })?;
        Ok(bincode::deserialize::<BPlusTreeNode<Self::K>>(&data[..])?)
    }
    fn read_trie_node(&self, trie_node_id: TrieNodeId) -> Result<TrieNode> {
        let data = self
            .trie_db
            .get(trie_node_id.to_le_bytes())?
            .context("failed to read trie node")?;
        Ok(bincode::deserialize::<TrieNode>(&data[..])?)
    }
    fn read_object(&self, obj_hash: Digest) -> Result<Object<Self::K>> {
        let data = self
            .obj_db
            .get(obj_hash.as_bytes())?
            .context("failed to read object")?;
        Ok(bincode::deserialize::<Object<Self::K>>(&data[..])?)
    }
}

impl WriteInterface for SimChain {
    type K = u32;
    fn set_parameter(&mut self, param: &Parameter) -> Result<()> {
        self.param = param.clone();
        let data = serde_json::to_string_pretty(&self.param)?;
        fs::write(self.root_path.join("param.json"), data)?;
        Ok(())
    }
    fn write_block_head(&mut self, blk_height: Height, block_head: &BlockHead) -> Result<()> {
        let bytes = bincode::serialize(block_head)?;
        self.block_head_db.put(blk_height.to_le_bytes(), bytes)?;
        Ok(())
    }
    fn write_block_content(
        &mut self,
        blk_height: Height,
        block_content: &BlockContent,
    ) -> Result<()> {
        let bytes = bincode::serialize(block_content)?;
        self.block_content_db.put(blk_height.to_le_bytes(), bytes)?;
        Ok(())
    }
    fn write_id_tree_node(&mut self, n_id: IdTreeNodeId, node: &IdTreeNode) -> Result<()> {
        let bytes = bincode::serialize(node)?;
        self.id_tree_db.put(n_id.to_le_bytes(), bytes)?;
        Ok(())
    }
    fn write_bplus_tree_node(
        &mut self,
        n_id: BPlusTreeNodeId,
        node: &BPlusTreeNode<Self::K>,
    ) -> Result<()> {
        let bytes = bincode::serialize(node)?;
        self.bplus_tree_db.put(n_id.to_le_bytes(), bytes)?;
        Ok(())
    }
    fn write_trie_node(&mut self, n_id: TrieNodeId, node: &TrieNode) -> Result<()> {
        let bytes = bincode::serialize(node)?;
        self.trie_db.put(n_id.to_le_bytes(), bytes)?;
        Ok(())
    }
    fn write_object(&mut self, obj_hash: Digest, obj: &Object<Self::K>) -> Result<()> {
        let bytes = bincode::serialize(obj)?;
        self.obj_db.put(obj_hash.as_bytes(), bytes)?;
        Ok(())
    }
}

impl WriteInterface for &mut SimChain {
    type K = u32;
    fn set_parameter(&mut self, param: &Parameter) -> Result<()> {
        self.param = param.clone();
        let data = serde_json::to_string_pretty(&self.param)?;
        fs::write(self.root_path.join("param.json"), data)?;
        Ok(())
    }
    fn write_block_head(&mut self, blk_height: Height, block_head: &BlockHead) -> Result<()> {
        let bytes = bincode::serialize(block_head)?;
        self.block_head_db.put(blk_height.to_le_bytes(), bytes)?;
        Ok(())
    }
    fn write_block_content(
        &mut self,
        blk_height: Height,
        block_content: &BlockContent,
    ) -> Result<()> {
        let bytes = bincode::serialize(block_content)?;
        self.block_content_db.put(blk_height.to_le_bytes(), bytes)?;
        Ok(())
    }
    fn write_id_tree_node(&mut self, n_id: IdTreeNodeId, node: &IdTreeNode) -> Result<()> {
        let bytes = bincode::serialize(node)?;
        self.id_tree_db.put(n_id.to_le_bytes(), bytes)?;
        Ok(())
    }
    fn write_bplus_tree_node(
        &mut self,
        n_id: BPlusTreeNodeId,
        node: &BPlusTreeNode<Self::K>,
    ) -> Result<()> {
        let bytes = bincode::serialize(node)?;
        self.bplus_tree_db.put(n_id.to_le_bytes(), bytes)?;
        Ok(())
    }
    fn write_trie_node(&mut self, n_id: TrieNodeId, node: &TrieNode) -> Result<()> {
        let bytes = bincode::serialize(node)?;
        self.trie_db.put(n_id.to_le_bytes(), bytes)?;
        Ok(())
    }
    fn write_object(&mut self, obj_hash: Digest, obj: &Object<Self::K>) -> Result<()> {
        let bytes = bincode::serialize(obj)?;
        self.obj_db.put(obj_hash.as_bytes(), bytes)?;
        Ok(())
    }
}

impl ScanQueryInterface for &SimChain {
    type K = u32;
    fn range_query(
        &self,
        query: Range<Self::K>,
        start_blk_height: Height,
        end_blk_height: Height,
        dim: usize,
    ) -> Result<HashSet<Digest>> {
        let mut res = HashSet::<Digest>::new();
        let db_iter = self.obj_db.iterator(rocksdb::IteratorMode::Start);
        for (_key, val) in db_iter {
            let o = bincode::deserialize::<Object<u32>>(&val[..])?;
            if o.blk_height <= end_blk_height && o.blk_height >= start_blk_height {
                let o_num_val = if let Some(n) = o.num_data.get(dim) {
                    *n
                } else {
                    0
                };
                if query.is_in_range(o_num_val) {
                    res.insert(o.to_digest());
                }
            }
        }
        Ok(res)
    }

    fn keyword_query(
        &self,
        keyword: &str,
        start_blk_height: Height,
        end_blk_height: Height,
    ) -> Result<HashSet<Digest>> {
        let mut res = HashSet::<Digest>::new();
        let db_iter = self.obj_db.iterator(rocksdb::IteratorMode::Start);
        for (_key, val) in db_iter {
            let o = bincode::deserialize::<Object<u32>>(&val[..])?;
            if o.blk_height <= end_blk_height && o.blk_height >= start_blk_height {
                for k in o.keyword_data.iter() {
                    if keyword == k {
                        res.insert(o.to_digest());
                    }
                }
            }
        }
        Ok(res)
    }

    fn root_query(&self, height: Height, win_size: u16) -> Result<HashSet<Digest>> {
        let mut res = HashSet::<Digest>::new();
        let db_iter = self.obj_db.iterator(rocksdb::IteratorMode::Start);
        for (_key, val) in db_iter {
            let o = bincode::deserialize::<Object<u32>>(&val[..])?;
            if o.blk_height <= height && o.blk_height.0 + win_size as u32 >= height.0 + 1 {
                res.insert(o.to_digest());
            }
        }
        Ok(res)
    }

    #[allow(clippy::type_complexity)]
    fn get_range_info(
        &self,
        start_blk_height: Height,
        end_blk_height: Height,
        dim_num: usize,
    ) -> Result<Vec<Range<Self::K>>> {
        let mut num_ranges = Vec::<Range<Self::K>>::new();
        let db_iter = self.obj_db.iterator(rocksdb::IteratorMode::Start);
        let mut num_range_scope = Vec::<(Self::K, Self::K)>::new();
        for _ in 0..dim_num {
            num_range_scope.push((std::u32::MAX, 0));
        }
        for (_key, val) in db_iter {
            let o = bincode::deserialize::<Object<u32>>(&val[..])?;
            if o.blk_height <= end_blk_height && o.blk_height >= start_blk_height {
                let o_num_vals = o.num_data;
                for (i, num_val) in o_num_vals.iter().enumerate() {
                    if i < dim_num {
                        let lower_bound = &num_range_scope
                            .get(i)
                            .with_context(|| {
                                format!("Object does not have numerical value at dim {}", i)
                            })?
                            .0;
                        let upper_bound = &num_range_scope
                            .get(i)
                            .with_context(|| {
                                format!("Object does not have numerical value at dim {}", i)
                            })?
                            .1;
                        if num_val < lower_bound {
                            num_range_scope
                                .get_mut(i)
                                .with_context(|| {
                                    format!("Object does not have numerical value at dim {}", i)
                                })?
                                .0 = *num_val;
                        } else if num_val > upper_bound {
                            num_range_scope
                                .get_mut(i)
                                .with_context(|| {
                                    format!("Object does not have numerical value at dim {}", i)
                                })?
                                .1 = *num_val;
                        }
                    }
                }
            }
        }

        for (min, max) in num_range_scope {
            num_ranges.push(Range::new(min, max));
        }

        Ok(num_ranges)
    }

    fn get_keyword_info(
        &self,
        start_blk_height: Height,
        end_blk_height: Height,
    ) -> Result<HashSet<String>> {
        let mut res = HashSet::<String>::new();
        let db_iter = self.obj_db.iterator(rocksdb::IteratorMode::Start);
        for (_key, val) in db_iter {
            let o = bincode::deserialize::<Object<u32>>(&val[..])?;
            if o.blk_height < end_blk_height && o.blk_height > start_blk_height {
                for k in o.keyword_data.iter() {
                    res.insert(k.to_string());
                }
            }
        }
        Ok(res)
    }
    fn get_chain_info(&self) -> Result<(u32, u32)> {
        let db_iter = self.obj_db.iterator(rocksdb::IteratorMode::Start);
        let mut cur_height_num = 0;
        let mut total_num = 0;
        for (_key, val) in db_iter {
            let o = bincode::deserialize::<Object<u32>>(&val[..])?;
            if cur_height_num < o.blk_height.0 {
                cur_height_num = o.blk_height.0;
            }
            total_num += 1;
        }
        Ok((total_num, cur_height_num))
    }
}
