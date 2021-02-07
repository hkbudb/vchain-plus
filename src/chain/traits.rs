use super::{
    block::{BlockContent, BlockHeader, BlockId},
    bplus_tree::{BPlusTreeNode, BPlusTreeNodeId},
    id_tree::{IdTreeNode, IdTreeNodeId},
    trie_tree::{TrieNode, TrieTreeNodeId},
};
use crate::digest::Digestible;
use anyhow::Result;
use std::fmt;

pub trait Num: num_traits::Num + Ord + Eq + Clone + Copy + fmt::Debug + Digestible {}

impl<T> Num for T where T: num_traits::Num + Ord + Eq + Clone + Copy + fmt::Debug + Digestible {}

pub trait ReadInterface {
    fn read_block_header(&self, block_id: BlockId) -> Result<BlockHeader>;
    fn read_block_content<K: Num>(&self, block_id: BlockId) -> Result<BlockContent<K>>;
    fn read_id_tree_node(&self, id_tree_node_id: IdTreeNodeId) -> Result<IdTreeNode>;
    fn read_bplus_tree_node<K: Num>(
        &self,
        bplus_tree_node_id: BPlusTreeNodeId,
    ) -> Result<BPlusTreeNode<K>>;
    fn read_trie_tree_node(&self, trie_node_id: TrieTreeNodeId) -> Result<TrieNode>;
    // fn read_object
}

pub trait WriteInterface {
    fn write_block_header(&mut self, block_header: BlockHeader) -> Result<()>;
    fn write_block_content<K: Num>(&mut self, block_content: BlockContent<K>) -> Result<()>;
    fn write_id_tree_node(&mut self, node: IdTreeNode) -> Result<()>;
    fn write_bplus_tree_node<K: Num>(&mut self, node: BPlusTreeNode<K>) -> Result<()>;
    fn write_trie_tree_node(&self, node: TrieNode) -> Result<()>;
    // fn write_object
}
