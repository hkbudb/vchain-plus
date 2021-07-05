use crate::{
    chain::{
        block::{BlockContent, BlockHead, Height},
        bplus_tree::{BPlusTreeNode, BPlusTreeNodeId, BPlusTreeNodeLoader},
        id_tree::{IdTreeNode, IdTreeNodeId, IdTreeNodeLoader},
        object::Object,
        trie_tree::TrieNodeLoader,
        trie_tree::{TrieNode, TrieNodeId},
        Parameter,
    },
    digest::{Digest, Digestible},
};
use anyhow::Result;
use core::str::FromStr;
use std::fmt;

pub trait Num:
    num_traits::Num + Ord + Eq + Clone + Copy + fmt::Debug + Digestible + FromStr
{
}

impl<T> Num for T where
    T: num_traits::Num + Ord + Eq + Clone + Copy + fmt::Debug + Digestible + FromStr
{
}

pub trait ReadInterface {
    type K: Num;
    fn get_parameter(&self) -> Result<Parameter>;
    fn read_block_head(&self, blk_heihgt: Height) -> Result<BlockHead>;
    fn read_block_content(&self, blk_height: Height) -> Result<BlockContent>;
    fn read_id_tree_node(&self, id_tree_node_id: IdTreeNodeId) -> Result<IdTreeNode>;
    fn read_bplus_tree_node(
        &self,
        bplus_tree_node_id: BPlusTreeNodeId,
    ) -> Result<BPlusTreeNode<Self::K>>;
    fn read_trie_node(&self, trie_node_id: TrieNodeId) -> Result<TrieNode>;
    fn read_object(&self, obj_hash: Digest) -> Result<Object<Self::K>>;
}

impl<Interface: ReadInterface> IdTreeNodeLoader for Interface {
    fn load_node(&self, id: IdTreeNodeId) -> Result<IdTreeNode> {
        self.read_id_tree_node(id)
    }
}

impl<Interface: ReadInterface> BPlusTreeNodeLoader<Interface::K> for Interface {
    fn load_node(&self, id: BPlusTreeNodeId) -> Result<BPlusTreeNode<Interface::K>> {
        self.read_bplus_tree_node(id)
    }
}

impl<Interface: ReadInterface> TrieNodeLoader for Interface {
    fn load_node(&self, id: TrieNodeId) -> Result<TrieNode> {
        self.read_trie_node(id)
    }
}

pub trait WriteInterface {
    type K: Num;
    fn set_parameter(&mut self, param: &Parameter) -> Result<()>;
    fn write_block_head(&mut self, blk_height: Height, block_head: &BlockHead) -> Result<()>;
    fn write_block_content(
        &mut self,
        blk_height: Height,
        block_content: &BlockContent,
    ) -> Result<()>;
    fn write_id_tree_node(&mut self, n_id: IdTreeNodeId, node: &IdTreeNode) -> Result<()>;
    fn write_bplus_tree_node(
        &mut self,
        n_id: BPlusTreeNodeId,
        node: &BPlusTreeNode<Self::K>,
    ) -> Result<()>;
    fn write_trie_node(&mut self, n_id: TrieNodeId, node: &TrieNode) -> Result<()>;
    fn write_object(&mut self, obj_hash: Digest, obj: &Object<Self::K>) -> Result<()>;
}
