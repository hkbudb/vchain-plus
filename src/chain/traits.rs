use super::{
    block::{BlockContent, BlockHead, BlockId},
    bplus_tree::{BPlusTreeNode, BPlusTreeNodeId},
    id_tree::{IdTreeNode, IdTreeNodeId},
    object::{ObjId, Object},
    trie_tree::{TrieNode, TrieTreeNodeId},
    Parameter,
};
use crate::digest::Digestible;
use anyhow::Result;
use std::fmt;

pub trait Num: num_traits::Num + Ord + Eq + Clone + Copy + fmt::Debug + Digestible {}

impl<T> Num for T where T: num_traits::Num + Ord + Eq + Clone + Copy + fmt::Debug + Digestible {}

pub trait ReadInterface {
    fn get_parameter(&self) -> Result<Parameter>;
    fn read_block_header(&self, block_id: BlockId) -> Result<BlockHead>;
    fn read_block_content(&self, block_id: BlockId) -> Result<BlockContent>;
    fn read_id_tree_node(&self, id_tree_node_id: IdTreeNodeId) -> Result<IdTreeNode>;
    fn read_bplus_tree_node<K: Num>(
        &self,
        bplus_tree_node_id: BPlusTreeNodeId,
    ) -> Result<BPlusTreeNode<K>>;
    fn read_trie_tree_node(&self, trie_node_id: TrieTreeNodeId) -> Result<TrieNode>;
    fn read_object<K: Num>(&self, id: ObjId) -> Result<Object<K>>;
}

pub trait WriteInterface {
    fn set_parameter(&mut self, param: Parameter) -> Result<()>;
    fn write_block_header(&mut self, block_header: BlockHead) -> Result<()>;
    fn write_block_content(&mut self, block_content: BlockContent) -> Result<()>;
    fn write_id_tree_node(&mut self, node: IdTreeNode) -> Result<()>;
    fn write_bplus_tree_node<K: Num>(&mut self, node: BPlusTreeNode<K>) -> Result<()>;
    fn write_trie_tree_node(&self, node: TrieNode) -> Result<()>;
    fn write_object<K: Num>(&self, obj: Object<K>) -> Result<()>;
}
