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
//use ark_ec::PairingEngine;

pub trait Num: num_traits::Num + Ord + Eq + Clone + Copy + fmt::Debug + Digestible {}

impl<T> Num for T where T: num_traits::Num + Ord + Eq + Clone + Copy + fmt::Debug + Digestible {}

pub trait ReadInterface<K: Num> {
    fn get_parameter(&self) -> Result<Parameter>;
    fn read_block_header(&self, block_id: BlockId) -> Result<BlockHead>;
    fn read_block_content(&self, block_id: BlockId) -> Result<BlockContent>;
    fn read_id_tree_node(&self, id_tree_node_id: IdTreeNodeId) -> Result<IdTreeNode>;
    fn read_bplus_tree_node(
        &self,
        bplus_tree_node_id: BPlusTreeNodeId,
    ) -> Result<BPlusTreeNode<K /*, E*/>>;
    fn read_trie_tree_node(&self, trie_node_id: TrieTreeNodeId) -> Result<TrieNode>;
    fn read_object(&self, id: ObjId) -> Result<Object<K>>;
}

pub trait WriteInterface<K: Num> {
    fn set_parameter(&mut self, param: Parameter) -> Result<()>;
    fn write_block_header(&mut self, block_header: BlockHead) -> Result<()>;
    fn write_block_content(&mut self, block_content: BlockContent) -> Result<()>;
    fn write_id_tree_node(&mut self, node: IdTreeNode) -> Result<()>;
    fn write_bplus_tree_node(&mut self, node: BPlusTreeNode<K /*, E*/>) -> Result<()>;
    fn write_trie_tree_node(&mut self, node: TrieNode) -> Result<()>;
    fn write_object(&mut self, obj: Object<K>) -> Result<()>;
}
