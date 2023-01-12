use super::{
    block::{build::build_block, BlockContent, BlockHead, Height},
    bplus_tree::{BPlusTreeNode, BPlusTreeNodeId},
    id_tree::{IdTreeNode, IdTreeNodeId},
    object::Object,
    range::Range,
    traits::{ReadInterface, ScanQueryInterface, WriteInterface},
    trie_tree::{TrieNode, TrieNodeId},
    Parameter,
};
use crate::{
    acc::{AccPublicKey, AccSecretKey, AccSecretKeyWithPowCache},
    chain::{
        query::{query, query_param::QueryParam},
        verify::verify,
    },
    digest::{Digest, Digestible},
    utils::{init_tracing_subscriber, load_raw_obj_from_str},
};
use anyhow::{Context, Result};
use once_cell::sync::Lazy;
use rand::{prelude::*, rngs::StdRng};
use serde_json::json;
use std::collections::{HashMap, HashSet};

const Q: u64 = 40;
static SEC_KEY: Lazy<AccSecretKeyWithPowCache> = Lazy::new(|| {
    let mut rng = StdRng::seed_from_u64(123_456_789u64);
    let sk = AccSecretKey::rand(&mut rng);
    sk.into()
});
pub(crate) static PUB_KEY: Lazy<AccPublicKey> = Lazy::new(|| AccPublicKey::gen_key(&(*SEC_KEY), Q));

#[derive(Debug, Default)]
struct FakeChain {
    param: Option<Parameter>,
    block_head: HashMap<Height, BlockHead>,
    block_content: HashMap<Height, BlockContent>,
    id_tree_nodes: HashMap<IdTreeNodeId, IdTreeNode>,
    bplus_tree_nodes: HashMap<BPlusTreeNodeId, BPlusTreeNode<u32>>,
    trie_nodes: HashMap<TrieNodeId, TrieNode>,
    objects: HashMap<Digest, Object<u32>>,
}

impl ReadInterface for &FakeChain {
    type K = u32;
    fn get_parameter(&self) -> Result<Parameter> {
        self.param.clone().context("failed to read parameter")
    }
    fn read_block_head(&self, blk_height: Height) -> Result<BlockHead> {
        self.block_head
            .get(&blk_height)
            .cloned()
            .context("failed to read block header")
    }
    fn read_block_content(&self, block_id: Height) -> Result<BlockContent> {
        self.block_content
            .get(&block_id)
            .cloned()
            .context("failed to read block content")
    }
    fn read_id_tree_node(&self, id_tree_node_id: IdTreeNodeId) -> Result<IdTreeNode> {
        self.id_tree_nodes
            .get(&id_tree_node_id)
            .cloned()
            .context("failed to read id tree node")
    }
    fn read_bplus_tree_node(
        &self,
        bplus_tree_node_id: BPlusTreeNodeId,
    ) -> Result<BPlusTreeNode<Self::K>> {
        self.bplus_tree_nodes
            .get(&bplus_tree_node_id)
            .cloned()
            .context(format!(
                "failed to read bplus tree node with id {:?}",
                bplus_tree_node_id
            ))
    }
    fn read_trie_node(&self, trie_node_id: TrieNodeId) -> Result<TrieNode> {
        self.trie_nodes
            .get(&trie_node_id)
            .cloned()
            .context("failed to read trie tree node")
    }
    fn read_object(&self, obj_hash: Digest) -> Result<Object<Self::K>> {
        self.objects
            .get(&obj_hash)
            .cloned()
            .context("failed to read object")
    }
}

impl ReadInterface for &mut FakeChain {
    type K = u32;
    fn get_parameter(&self) -> Result<Parameter> {
        self.param.clone().context("failed to read parameter")
    }
    fn read_block_head(&self, blk_height: Height) -> Result<BlockHead> {
        self.block_head
            .get(&blk_height)
            .cloned()
            .context("failed to read block header")
    }
    fn read_block_content(&self, block_id: Height) -> Result<BlockContent> {
        self.block_content
            .get(&block_id)
            .cloned()
            .context("failed to read block content")
    }
    fn read_id_tree_node(&self, id_tree_node_id: IdTreeNodeId) -> Result<IdTreeNode> {
        self.id_tree_nodes
            .get(&id_tree_node_id)
            .cloned()
            .context("failed to read id tree node")
    }
    fn read_bplus_tree_node(
        &self,
        bplus_tree_node_id: BPlusTreeNodeId,
    ) -> Result<BPlusTreeNode<Self::K>> {
        self.bplus_tree_nodes
            .get(&bplus_tree_node_id)
            .cloned()
            .context(format!(
                "failed to read bplus tree node with id {:?}",
                bplus_tree_node_id
            ))
    }
    fn read_trie_node(&self, trie_node_id: TrieNodeId) -> Result<TrieNode> {
        self.trie_nodes
            .get(&trie_node_id)
            .cloned()
            .context("failed to read trie tree node")
    }
    fn read_object(&self, obj_hash: Digest) -> Result<Object<Self::K>> {
        self.objects
            .get(&obj_hash)
            .cloned()
            .context("failed to read object")
    }
}

impl WriteInterface for FakeChain {
    type K = u32;
    fn set_parameter(&mut self, param: &Parameter) -> Result<()> {
        self.param = Some(param.clone());
        Ok(())
    }
    fn write_block_head(&mut self, blk_height: Height, blk_head: &BlockHead) -> Result<()> {
        self.block_head.insert(blk_height, blk_head.clone());
        Ok(())
    }
    fn write_block_content(
        &mut self,
        blk_height: Height,
        blk_content: &BlockContent,
    ) -> Result<()> {
        self.block_content.insert(blk_height, blk_content.clone());
        Ok(())
    }
    fn write_id_tree_node(&mut self, id: IdTreeNodeId, node: &IdTreeNode) -> Result<()> {
        self.id_tree_nodes.insert(id, node.clone());
        Ok(())
    }
    fn write_bplus_tree_node(
        &mut self,
        id: BPlusTreeNodeId,
        node: &BPlusTreeNode<Self::K>,
    ) -> Result<()> {
        self.bplus_tree_nodes.insert(id, node.clone());
        Ok(())
    }
    fn write_trie_node(&mut self, id: TrieNodeId, node: &TrieNode) -> Result<()> {
        self.trie_nodes.insert(id, node.clone());
        Ok(())
    }
    fn write_object(&mut self, obj_hash: Digest, obj: &Object<Self::K>) -> Result<()> {
        self.objects.insert(obj_hash, obj.clone());
        Ok(())
    }
}

impl WriteInterface for &mut FakeChain {
    type K = u32;
    fn set_parameter(&mut self, param: &Parameter) -> Result<()> {
        self.param = Some(param.clone());
        Ok(())
    }
    fn write_block_head(&mut self, blk_height: Height, blk_head: &BlockHead) -> Result<()> {
        self.block_head.insert(blk_height, blk_head.clone());
        Ok(())
    }
    fn write_block_content(
        &mut self,
        blk_height: Height,
        blk_content: &BlockContent,
    ) -> Result<()> {
        self.block_content.insert(blk_height, blk_content.clone());
        Ok(())
    }
    fn write_id_tree_node(&mut self, id: IdTreeNodeId, node: &IdTreeNode) -> Result<()> {
        self.id_tree_nodes.insert(id, node.clone());
        Ok(())
    }
    fn write_bplus_tree_node(
        &mut self,
        id: BPlusTreeNodeId,
        node: &BPlusTreeNode<Self::K>,
    ) -> Result<()> {
        self.bplus_tree_nodes.insert(id, node.clone());
        Ok(())
    }
    fn write_trie_node(&mut self, id: TrieNodeId, node: &TrieNode) -> Result<()> {
        self.trie_nodes.insert(id, node.clone());
        Ok(())
    }
    fn write_object(&mut self, obj_hash: Digest, obj: &Object<Self::K>) -> Result<()> {
        self.objects.insert(obj_hash, obj.clone());
        Ok(())
    }
}

impl ScanQueryInterface for &FakeChain {
    type K = u32;
    fn range_query(
        &self,
        query: Range<Self::K>,
        start_blk_height: Height,
        end_blk_height: Height,
        dim: usize,
    ) -> Result<HashSet<Digest>> {
        let mut res = HashSet::<Digest>::new();
        for (hash, o) in &self.objects {
            if o.blk_height <= end_blk_height && o.blk_height >= start_blk_height {
                let o_num_val = o.num_data.get(dim).with_context(|| {
                    format!("Object does not have numerical value at dim {}", dim)
                })?;
                if query.is_in_range(*o_num_val) {
                    res.insert(*hash);
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
        for (hash, o) in &self.objects {
            if o.blk_height <= end_blk_height && o.blk_height >= start_blk_height {
                for k in o.keyword_data.iter() {
                    if keyword == k {
                        res.insert(*hash);
                    }
                }
            }
        }
        Ok(res)
    }

    fn root_query(&self, height: Height, win_size: u16) -> Result<HashSet<Digest>> {
        let mut res = HashSet::<Digest>::new();
        for (hash, o) in &self.objects {
            if o.blk_height <= height
                && Height(o.blk_height.0 + win_size as u32) >= Height(height.0 + 1)
            {
                res.insert(*hash);
            }
        }
        Ok(res)
    }

    fn get_range_info(
        &self,
        start_blk_height: Height,
        end_blk_height: Height,
        dim_num: usize,
    ) -> Result<Vec<Range<Self::K>>> {
        let mut num_ranges = Vec::<Range<Self::K>>::new();
        let mut num_range_scope = Vec::<(Self::K, Self::K)>::new();
        for _ in 0..dim_num {
            num_range_scope.push((std::u32::MAX, 0));
        }
        for (_hash, o) in &self.objects {
            if o.blk_height < end_blk_height && o.blk_height > start_blk_height {
                let o_num_vals = &o.num_data;
                for (i, num_val) in o_num_vals.iter().enumerate() {
                    if i < dim_num {
                        if num_val
                            < &num_range_scope
                                .get(i)
                                .with_context(|| {
                                    format!("Object does not have numerical value at dim {}", i)
                                })?
                                .0
                        {
                            num_range_scope
                                .get_mut(i)
                                .with_context(|| {
                                    format!("Object does not have numerical value at dim {}", i)
                                })?
                                .0 = *num_val;
                        } else if num_val
                            > &num_range_scope
                                .get(i)
                                .with_context(|| {
                                    format!("Object does not have numerical value at dim {}", i)
                                })?
                                .1
                        {
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
        for (_, o) in &self.objects {
            if o.blk_height < end_blk_height && o.blk_height > start_blk_height {
                for k in o.keyword_data.iter() {
                    res.insert(k.to_string());
                }
            }
        }
        Ok(res)
    }

    fn get_chain_info(&self) -> Result<(u32, u32)> {
        let mut cur_height_num = 0;
        let mut total_num = 0;
        for (_, o) in &self.objects {
            if cur_height_num < o.blk_height.0 {
                cur_height_num = o.blk_height.0;
            }
            total_num += 1;
        }
        Ok((total_num, cur_height_num))
    }
}

impl FakeChain {
    fn new() -> Self {
        Self {
            param: None,
            block_head: HashMap::<Height, BlockHead>::new(),
            block_content: HashMap::<Height, BlockContent>::new(),
            id_tree_nodes: HashMap::<IdTreeNodeId, IdTreeNode>::new(),
            bplus_tree_nodes: HashMap::<BPlusTreeNodeId, BPlusTreeNode<u32>>::new(),
            trie_nodes: HashMap::<TrieNodeId, TrieNode>::new(),
            objects: HashMap::<Digest, Object<u32>>::new(),
        }
    }
}

fn build_chain(data: &str, param: &Parameter) -> Result<FakeChain> {
    let mut chain = FakeChain::new();
    chain.set_parameter(param)?;
    let mut prev_hash = Digest::zero();
    for (blk_height, objs) in load_raw_obj_from_str(data)? {
        let (blk_head, _duration) =
            build_block(blk_height, prev_hash, objs, &mut chain, &param, &PUB_KEY)?;
        prev_hash = blk_head.to_digest();
    }
    Ok(chain)
}

const TEST_DATA_1: &str = r#"
1 [ 1 ] { a }
1 [ 2 ] { ab }
1 [ 3 ] { ced }
1 [ 4 ] { a }
2 [ 2 ] { bc }
2 [ 2 ] { b }
2 [ 3 ] { bdae }
2 [ 4 ] { acd }
3 [ 4 ] { ae }
3 [ 2 ] { dc }
3 [ 3 ] { aed }
3 [ 1 ] { acd }
"#;

const TEST_DATA_2: &str = r#"
1 [ 7, 2 ] { a }
1 [ 9, 5 ] { ab, c }
1 [ 2, 4 ] { ced }
1 [ 8, 8 ] { a, b, c }
2 [ 1, 4 ] { bc }
2 [ 10, 7 ] { b, c, d }
2 [ 11, 2 ] { b, c }
2 [ 5, 8 ] { acd, c, b }
3 [ 3, 9 ] { ae, b, c }
3 [ 12, 4 ] { dc }
3 [ 6, 6 ] { aed, a }
3 [ 4, 9 ] { b }
4 [ 4, 2 ] { c }
4 [ 3, 8 ] { a }
4 [ 6, 12 ] { b }
4 [ 5, 7 ] { a, b, c }
"#;

const TEST_DATA_3: &str = r#"
1 [ 7, 2 ] { a }
1 [ 9, 5 ] { ab, c }
1 [ 2, 4 ] { ced }
1 [ 8, 8 ] { a, b, c }
2 [ 1, 4 ] { bc }
2 [ 10, 7 ] { b, c, d }
2 [ 11, 2 ] { b, c }
2 [ 5, 8 ] { acd, c, b }
3 [ 3, 9 ] { ae, b, c }
3 [ 12, 4 ] { dc }
3 [ 6, 6 ] { aed, a }
3 [ 4, 9 ] { b }
4 [ 4, 2 ] { c }
4 [ 3, 8 ] { a }
4 [ 6, 12 ] { b }
4 [ 5, 7 ] { a, b, c }
5 [ 6, 9 ] { d, a }
5 [ 10, 1 ] { ae, dc }
5 [ 15, 11 ] { d }
5 [ 11, 12 ] { a, e }
6 [ 7, 3 ] { b, c, e, f }
6 [ 11, 2 ] { d, e }
6 [ 10, 6 ] { a }
6 [ 6, 5 ] { b, e, f }
7 [ 8, 8 ] { b, c, a}
7 [ 5, 12 ] { a }
7 [ 13, 12 ] { bc }
7 [ 12, 8 ] { e }
8 [ 13, 8 ] { fe, c }
8 [ 6, 6 ] { a, b }
8 [ 1, 2 ] { d, b, e }
8 [ 6, 7 ] { a, f }
9 [ 5, 8 ] { d, b, c }
9 [ 7, 9 ] { e, a, c }
9 [ 2, 13 ] { b }
9 [ 6, 9 ] { e, d }
10 [ 9, 14 ] { a }
10 [ 2, 12 ] { c, d, b }
10 [ 5, 10 ] { e, b, a }
10 [ 8, 12 ] { c, b }
"#;

#[test]
fn test_fake_chain_write() {
    let param = Parameter {
        time_win_sizes: vec![2],
        id_tree_fanout: 2,
        max_id_num: 16,
        bplus_tree_fanout: 3,
        num_dim: 1,
    };
    let test_chain1 = build_chain(TEST_DATA_1, &param).unwrap();
    println!("{:#?}", test_chain1);

    let param = Parameter {
        time_win_sizes: vec![2, 3],
        id_tree_fanout: 2,
        max_id_num: 32,
        bplus_tree_fanout: 3,
        num_dim: 2,
    };
    let test_chain2 = build_chain(TEST_DATA_2, &param).unwrap();
    println!("{:#?}", test_chain2);
    assert_eq!(1, 1);
}

#[test]
fn test_fake_chain_read_basic() -> Result<()> {
    init_tracing_subscriber("info")?;
    let param = Parameter {
        time_win_sizes: vec![4],
        id_tree_fanout: 4,
        max_id_num: 32,
        bplus_tree_fanout: 4,
        num_dim: 2,
    };
    let test_chain = build_chain(TEST_DATA_3, &param).unwrap();
    let query1_param_data = json!({
        "start_blk": 2,
        "end_blk": 4,
        "range": [(1, 7), (2, 9)],
        "keyword_exp": {
            "or": [
                {"input": "a"},
                {"and": [{"input": "b"}, {"input": "c"}]},
            ]
        },
    });
    let query1_param: QueryParam<u32> = serde_json::from_value(query1_param_data).unwrap();
    let (results, dag_map, _time) =
        query(false, false, &test_chain, query1_param, &PUB_KEY).unwrap();
    println!("results for query 1: ");
    for (res, _vo) in &results {
        println!("{:#?}", res);
    }
    verify(&test_chain, &results, &dag_map, &PUB_KEY).unwrap();

    let query2_param_data = json!({
        "start_blk": 1,
        "end_blk": 4,
        "range": [(1, 7), (2, 9)],
        "keyword_exp": {
            "or": [
                {"input": "a"},
                {"and": [{"input": "b"}, {"input": "c"}]},
            ]
        },
    });
    let query2_param: QueryParam<u32> = serde_json::from_value(query2_param_data).unwrap();
    let (results, dag_map, _time) =
        query(false, false, &test_chain, query2_param, &PUB_KEY).unwrap();
    println!("results for query 2: ");
    for (res, _vo) in &results {
        println!("{:#?}", res);
    }
    verify(&test_chain, &results, &dag_map, &PUB_KEY).unwrap();
    assert_eq!(1, 1);
    Ok(())
}
