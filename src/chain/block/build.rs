use crate::{
    acc::{AccPublicKey, AccValue, Set},
    chain::{
        block::{
            block_ads::BlockMultiADS,
            hash::{ads_root_hash, obj_id_nums_hash, obj_root_hash},
            BlockContent, BlockHead, Height,
        },
        bplus_tree::{self, BPlusTreeNode, BPlusTreeNodeId, BPlusTreeRoot},
        id_tree::{self, ObjId},
        object::Object,
        traits::{Num, ReadInterface, WriteInterface},
        trie_tree::{self, TrieNode, TrieNodeId, TrieRoot},
        Parameter,
    },
    digest::{Digest, Digestible},
};
use anyhow::{bail, Context, Result};
use howlong::ProcessDuration;
use smol_str::SmolStr;
use std::{collections::HashMap, num::NonZeroU64};

pub fn build_block<K: Num, T: ReadInterface<K = K> + WriteInterface<K = K>>(
    blk_height: Height,
    prev_hash: Digest,
    raw_objs: Vec<Object<K>>,
    mut chain: T,
    param: &Parameter,
    pk: &AccPublicKey,
) -> Result<(BlockHead, ProcessDuration)> {
    info!("Building block {}...", blk_height);
    let timer = howlong::ProcessCPUTimer::new();
    let mut block_head = BlockHead {
        blk_height,
        prev_hash,
        ..Default::default()
    };
    let mut block_content = BlockContent::new(blk_height, prev_hash);
    let max_id_num = param.max_id_num;
    let mut blk_multi_ads: BlockMultiADS = BlockMultiADS::default();
    debug!("trying to get pre_k-th block content");
    let pre_blk_content = if blk_height.0 > 1 {
        chain.read_block_content(Height(blk_height.0 - 1))?
    } else {
        BlockContent::default()
    };

    let multi_ads = pre_blk_content.ads.read_adses();
    let time_wins = &param.time_win_sizes;

    debug!("initializing tree ctxes");
    // id tree ctx
    let id_tree_root = pre_blk_content.id_tree_root;
    let mut id_tree_ctx = id_tree::write::WriteContext::new(&chain, id_tree_root);
    // trie ctxes
    let mut trie_ctxes = Vec::<(u64, trie_tree::write::WriteContext<T>)>::new();
    // bplus tree
    let mut bplus_ctxes = Vec::<(u64, Vec<bplus_tree::write::WriteContext<K, T>>)>::new();

    for &k in time_wins {
        let pre_k_blk_content = if blk_height.0 > k {
            chain.read_block_content(Height(blk_height.0 - k))?
        } else {
            BlockContent::default()
        };
        let pre_k_blk_obj_hashes = &pre_k_blk_content.obj_hashes;
        let pre_k_blk_obj_id_nums = &pre_k_blk_content.obj_id_nums;

        // trie part
        let trie_root = if let Some(block_ads) = multi_ads.get(&k) {
            block_ads.trie_root
        } else {
            TrieRoot::default()
        };
        let mut trie_ctx = trie_tree::write::WriteContext::new(&chain, trie_root);
        for (idx, obj_hash) in pre_k_blk_obj_hashes.iter().enumerate() {
            let raw_obj = chain.read_object(*obj_hash)?;
            let obj_id_num = pre_k_blk_obj_id_nums
                .get(idx)
                .context("Cannot find object id number!")?;
            for key in &raw_obj.keyword_data {
                trie_ctx.delete(SmolStr::from(key), ObjId(*obj_id_num), pk)?;
            }
        }
        trie_ctxes.push((k, trie_ctx));
        debug!("finish trie delete from pre_k-th block");

        //bplus tree part
        let mut bplus_ctx_vec = Vec::<bplus_tree::write::WriteContext<K, T>>::new();
        for dim in 0..param.num_dim {
            debug!(
                "processing bplus tree delete from pre_k-th block for dim {}",
                dim
            );
            let bplus_tree_root = if let Some(block_ads) = multi_ads.get(&k) {
                if let Some(bplus_root) = block_ads.bplus_tree_roots.get(dim) {
                    *bplus_root
                } else {
                    bail!(
                        "Cannot find BPlusRoot for dimension {} in time window {}!",
                        dim,
                        k
                    );
                }
            } else {
                BPlusTreeRoot::default()
            };
            let mut bplus_ctx = bplus_tree::write::WriteContext::new(&chain, bplus_tree_root);
            for (idx, obj_hash) in pre_k_blk_obj_hashes.iter().enumerate() {
                let raw_obj = chain.read_object(*obj_hash)?;
                let obj_id_num = pre_k_blk_obj_id_nums
                    .get(idx)
                    .context("Cannot find object id number!")?;
                if let Some(num_data) = raw_obj.num_data.get(dim) {
                    bplus_ctx.delete(*num_data, ObjId(*obj_id_num), param.bplus_tree_fanout, pk)?;
                }
            }
            bplus_ctx_vec.push(bplus_ctx);
        }
        bplus_ctxes.push((k, bplus_ctx_vec));
        debug!("finish bplus tree delete from pre_k-th block");
    }

    let mut obj_hashes = Vec::<Digest>::new();
    let mut obj_id_nums = Vec::<NonZeroU64>::new();

    debug!("start inserting");
    for obj in &raw_objs {
        debug!("inserting for obj {:?}", obj);
        // build id tree
        let obj_hash = obj.to_digest();
        let obj_id = id_tree_ctx.insert(obj_hash, max_id_num as usize, param.id_tree_fanout)?;
        debug!("inserting for id tree finished");
        // build trie
        for (_k, trie_ctx) in &mut trie_ctxes {
            for key in &obj.keyword_data {
                trie_ctx.insert(SmolStr::from(key), obj_id, pk)?;
            }
        }
        debug!("inserting for trie finished");
        // build bplus tree
        for (_k, bplus_ctx_vec) in &mut bplus_ctxes {
            for (dim, bplus_ctx) in bplus_ctx_vec.iter_mut().enumerate() {
                debug!("processing dim {}", dim);
                if let Some(key) = obj.num_data.get(dim) {
                    bplus_ctx.insert(*key, obj_id, param.bplus_tree_fanout, pk)?;
                }
            }
        }
        debug!("inserting for bplus tree finished");
        obj_hashes.push(obj.to_digest());
        obj_id_nums.push(obj_id.0);
    }
    debug!("finish tree insert");

    // handle id tree changes
    let id_tree_changes = id_tree_ctx.changes();
    debug!("finish id tree ctx change update");

    // handle trie changes
    let mut new_trie_nodes = Vec::<HashMap<TrieNodeId, TrieNode>>::new();
    let mut new_trie_roots = Vec::<(u64, TrieRoot)>::new();
    for (k, trie_ctx) in trie_ctxes {
        let trie_changes = trie_ctx.changes();
        new_trie_roots.push((k, trie_changes.root));
        new_trie_nodes.push(trie_changes.nodes);
    }
    blk_multi_ads.set_multi_trie_roots(new_trie_roots.iter());
    debug!("finish trie ctx change update");

    // handle bplus tree changes
    let mut new_bplus_roots = Vec::<(u64, Vec<BPlusTreeRoot>)>::new();
    let mut new_bplus_nodes = Vec::<HashMap<BPlusTreeNodeId, BPlusTreeNode<K>>>::new();
    for (k, bplus_ctx_vec) in bplus_ctxes {
        let mut new_bplus_roots_dim = Vec::<BPlusTreeRoot>::new();
        for bplus_ctx in bplus_ctx_vec {
            let bplus_tree_changes = bplus_ctx.changes();
            new_bplus_roots_dim.push(bplus_tree_changes.root);
            new_bplus_nodes.push(bplus_tree_changes.nodes);
        }
        new_bplus_roots.push((k, new_bplus_roots_dim));
    }
    blk_multi_ads.set_multi_bplus_roots(new_bplus_roots.iter());
    debug!("finish bplus tree ctx change update");

    // write nodes to chain
    for (id, node) in id_tree_changes.nodes {
        chain.write_id_tree_node(id, &node)?;
    }
    for map in new_trie_nodes {
        for (id, node) in map {
            chain.write_trie_node(id, &node)?;
        }
    }
    for map in new_bplus_nodes {
        for (id, node) in map {
            chain.write_bplus_tree_node(id, &node)?;
        }
    }
    debug!("finish writing nodes to chain");

    // write objs to chain
    for obj in raw_objs {
        chain.write_object(obj.to_digest(), &obj)?;
    }
    debug!("finish writing objects to chain");

    let obj_root_hash = obj_root_hash(obj_hashes.iter());
    let id_set_root_hash = obj_id_nums_hash(obj_id_nums.iter());
    let ads_hash = blk_multi_ads.to_digest();
    let ads_root_hash = ads_root_hash(
        &id_set_root_hash,
        &id_tree_changes.root.to_digest(),
        &ads_hash,
    );

    block_head.set_obj_root_hash(obj_root_hash);
    block_head.set_ads_root_hash(ads_root_hash);

    let obj_id_nums_iter = obj_id_nums.clone().into_iter();
    let root_id_set: Set = obj_id_nums_iter.collect();
    let root_acc = AccValue::from_set(&root_id_set, pk);

    block_content.set_multi_ads(blk_multi_ads);
    block_content.set_obj_hashes(obj_hashes);
    block_content.set_obj_id_nums(obj_id_nums);
    block_content.set_id_tree_root(id_tree_changes.root);
    block_content.set_acc(Some(root_acc));

    chain.write_block_content(blk_height, &block_content)?;
    chain.write_block_head(blk_height, &block_head)?;
    let time = timer.elapsed();
    info!("Time elapsed : {}.", time);

    Ok((block_head, time))
}
