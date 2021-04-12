use std::collections::HashMap;

use anyhow::Context;

use super::{
    block::{BlockContent, BlockHead, BlockId},
    bplus_tree::{BPlusTreeNode, BPlusTreeNodeId},
    id_tree::{IdTreeNode, IdTreeNodeId},
    object::{ObjId, Object},
    traits::{Num, ReadInterface, WriteInterface},
    trie_tree::{TrieNode, TrieTreeNodeId},
    Parameter,
};
use ark_ec::PairingEngine;

#[derive(Debug, Default)]
struct FakeChain<K: Num, E: PairingEngine> {
    param: Option<Parameter>,
    block_head: HashMap<BlockId, BlockHead>,
    block_content: HashMap<BlockId, BlockContent>,
    id_tree_nodes: HashMap<IdTreeNodeId, IdTreeNode>,
    bplus_tree_nodes: HashMap<BPlusTreeNodeId, BPlusTreeNode<K, E>>,
    trie_tree_nodes: HashMap<TrieTreeNodeId, TrieNode>,
    objects: HashMap<ObjId, Object<K>>,
}

impl<K: Num, E: PairingEngine> ReadInterface<K, E> for FakeChain<K, E> {
    fn get_parameter(&self) -> anyhow::Result<Parameter> {
        self.param.clone().context("failed to get param")
    }

    fn read_block_header(&self, block_id: BlockId) -> anyhow::Result<BlockHead> {
        self.block_head
            .get(&block_id)
            .cloned()
            .context("failed to read block header")
    }

    fn read_block_content(&self, block_id: BlockId) -> anyhow::Result<BlockContent> {
        self.block_content
            .get(&block_id)
            .cloned()
            .context("failed to read block content")
    }

    fn read_id_tree_node(&self, id_tree_node_id: IdTreeNodeId) -> anyhow::Result<IdTreeNode> {
        self.id_tree_nodes
            .get(&id_tree_node_id)
            .cloned()
            .context("failed to read id tree node")
    }

    fn read_bplus_tree_node(
        &self,
        bplus_tree_node_id: BPlusTreeNodeId,
    ) -> anyhow::Result<BPlusTreeNode<K, E>> {
        self.bplus_tree_nodes
            .get(&bplus_tree_node_id)
            .cloned()
            .context("failed to read bplus tree node")
    }

    fn read_trie_tree_node(&self, trie_node_id: TrieTreeNodeId) -> anyhow::Result<TrieNode> {
        self.trie_tree_nodes
            .get(&trie_node_id)
            .cloned()
            .context("failed to read trie tree node")
    }

    fn read_object(&self, id: ObjId) -> anyhow::Result<Object<K>> {
        self.objects
            .get(&id)
            .cloned()
            .context("failed to read object")
    }
}

impl<K: Num, E: PairingEngine> WriteInterface<K, E> for FakeChain<K, E> {
    fn set_parameter(&mut self, param: Parameter) -> anyhow::Result<()> {
        self.param = Some(param);
        Ok(())
    }

    fn write_block_header(&mut self, block_header: BlockHead) -> anyhow::Result<()> {
        let id = block_header.block_id;
        self.block_head.insert(id, block_header);
        Ok(())
    }

    fn write_block_content(&mut self, block_content: BlockContent) -> anyhow::Result<()> {
        let id = block_content.block_id;
        self.block_content.insert(id, block_content);
        Ok(())
    }

    fn write_id_tree_node(&mut self, node: IdTreeNode) -> anyhow::Result<()> {
        let id = node.get_node_id();
        self.id_tree_nodes.insert(id, node);
        Ok(())
    }

    fn write_bplus_tree_node(&mut self, node: BPlusTreeNode<K, E>) -> anyhow::Result<()> {
        let id = node.get_node_id();
        self.bplus_tree_nodes.insert(id, node);
        Ok(())
    }

    fn write_trie_tree_node(&mut self, node: TrieNode) -> anyhow::Result<()> {
        let id = node.get_node_id();
        self.trie_tree_nodes.insert(id, node);
        Ok(())
    }

    fn write_object(&mut self, obj: Object<K>) -> anyhow::Result<()> {
        let id = obj.id;
        self.objects.insert(id, obj);
        Ok(())
    }
}
