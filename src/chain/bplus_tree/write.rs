use crate::{
    acc::{AccPublicKey, AccValue, Set},
    chain::{
        bplus_tree::{
            BPlusTreeLeafNode, BPlusTreeNode, BPlusTreeNodeId, BPlusTreeNodeLoader,
            BPlusTreeNonLeafNode, BPlusTreeRoot, Digest, Digestible,
        },
        id_tree::ObjId,
        range::Range,
        traits::Num,
        MAX_INLINE_BTREE_FANOUT,
    },
};
use anyhow::{anyhow, bail, Context, Result};
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Apply<K: Num> {
    pub root: BPlusTreeRoot,
    pub nodes: HashMap<BPlusTreeNodeId, BPlusTreeNode<K>>,
}

pub struct WriteContext<'a, K: Num, L: BPlusTreeNodeLoader<K>> {
    node_loader: &'a L,
    apply: Apply<K>,
    outdated: HashSet<BPlusTreeNodeId>,
}

impl<'a, K: Num, L: BPlusTreeNodeLoader<K>> WriteContext<'a, K, L> {
    pub fn new(node_loader: &'a L, root: BPlusTreeRoot) -> Self {
        Self {
            node_loader,
            apply: Apply {
                root,
                nodes: HashMap::new(),
            },
            outdated: HashSet::new(),
        }
    }

    pub fn changes(self) -> Apply<K> {
        self.apply
    }

    pub fn write_leaf(
        &mut self,
        num: K,
        data_set: Set,
        acc: AccValue,
    ) -> (BPlusTreeNodeId, Digest) {
        let n = BPlusTreeLeafNode::new(num, data_set, acc);
        let id = n.id;
        let hash = n.to_digest();
        self.apply.nodes.insert(id, BPlusTreeNode::from_leaf(n));
        (id, hash)
    }

    pub fn write_non_leaf(&mut self, n: BPlusTreeNonLeafNode<K>) -> (BPlusTreeNodeId, Digest) {
        let id = n.id;
        let hash = n.to_digest();
        self.apply.nodes.insert(id, BPlusTreeNode::from_non_leaf(n));
        (id, hash)
    }

    fn get_node(&self, id: BPlusTreeNodeId) -> Result<Cow<BPlusTreeNode<K>>> {
        Ok(match self.apply.nodes.get(&id) {
            Some(n) => Cow::Borrowed(n),
            None => Cow::Owned(self.node_loader.load_node(id)?),
        })
    }

    pub fn insert(&mut self, key: K, obj_id: ObjId, fanout: u8, pk: &AccPublicKey) -> Result<()> {
        let set = Set::from_single_element(obj_id.0);
        let new_acc = AccValue::from_set(&set, pk);

        let mut cur_id_opt = self.apply.root.bplus_tree_root_id;
        let mut insert_flag = false;
        let mut update_flag = false;

        #[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
        enum TempNode<N: Num> {
            Leaf {
                id: BPlusTreeNodeId,
                hash: Digest,
            },
            NonLeaf {
                node: BPlusTreeNonLeafNode<N>,
                idx: usize,
            },
        }
        let mut temp_nodes: Vec<TempNode<K>> = Vec::new();
        let mut c_id: BPlusTreeNodeId = BPlusTreeNodeId::next_id();

        'outer: loop {
            match cur_id_opt {
                Some(id) => {
                    self.outdated.insert(id);
                    let cur_node = self.get_node(id)?;
                    match cur_node.as_ref() {
                        BPlusTreeNode::Leaf(n) => {
                            let old_num = n.num;
                            let old_data_set = n.data_set.clone();
                            let old_acc = n.data_set_acc;
                            let set_union = &n.data_set | &set;
                            if old_num == key {
                                let (id, hash) = self.write_leaf(key, set_union, old_acc + new_acc);
                                temp_nodes.push(TempNode::Leaf { id, hash });
                                break;
                            }
                            let new_range = if old_num < key {
                                Range::new(old_num, key)
                            } else {
                                Range::new(key, old_num)
                            };

                            let non_leaf = BPlusTreeNonLeafNode::new(
                                new_range,
                                set_union,
                                old_acc + new_acc,
                                SmallVec::<[Digest; MAX_INLINE_BTREE_FANOUT]>::new(),
                                SmallVec::<[BPlusTreeNodeId; MAX_INLINE_BTREE_FANOUT]>::new(),
                            );
                            temp_nodes.push(TempNode::NonLeaf {
                                node: non_leaf,
                                idx: 0,
                            });
                            let (old_leaf_id, old_leaf_hash) =
                                self.write_leaf(old_num, old_data_set, old_acc);
                            let (new_leaf_id, new_leaf_hash) = self.write_leaf(key, set, new_acc);
                            if old_num < key {
                                temp_nodes.push(TempNode::Leaf {
                                    id: old_leaf_id,
                                    hash: old_leaf_hash,
                                });
                                temp_nodes.push(TempNode::Leaf {
                                    id: new_leaf_id,
                                    hash: new_leaf_hash,
                                });
                            } else {
                                temp_nodes.push(TempNode::Leaf {
                                    id: new_leaf_id,
                                    hash: new_leaf_hash,
                                });
                                temp_nodes.push(TempNode::Leaf {
                                    id: old_leaf_id,
                                    hash: old_leaf_hash,
                                });
                            }
                            break;
                        }
                        BPlusTreeNode::NonLeaf(n) => {
                            let set_union = &n.data_set | &set;
                            let child_ids = n.child_ids.clone();
                            let child_hashes = n.child_hashes.clone();
                            let old_acc = n.data_set_acc;

                            let mut right_flag = false;
                            let new_range: Range<K>;
                            if n.range.is_in_range(key) {
                                new_range = n.range;
                            } else if key < n.range.get_low() {
                                new_range = Range::new(key, n.range.get_high());
                            } else {
                                new_range = Range::new(n.range.get_low(), key);
                                right_flag = true;
                            }

                            let idx: usize;
                            let child_len: usize = child_ids.len();

                            for (cur_child_idx, child) in child_ids.clone().into_iter().enumerate()
                            {
                                if right_flag {
                                    idx = child_len - 1;
                                    let child_node = self.get_node(child)?;
                                    match child_node.as_ref() {
                                        BPlusTreeNode::Leaf(_node) => {
                                            temp_nodes.push(TempNode::NonLeaf {
                                                node: BPlusTreeNonLeafNode::new(
                                                    new_range,
                                                    set_union,
                                                    old_acc + new_acc,
                                                    child_hashes,
                                                    child_ids,
                                                ),
                                                idx: idx + 1,
                                            });
                                            let (new_leaf_id, new_leaf_hash) =
                                                self.write_leaf(key, set, new_acc);
                                            temp_nodes.push(TempNode::Leaf {
                                                id: new_leaf_id,
                                                hash: new_leaf_hash,
                                            });
                                            break 'outer;
                                        }
                                        BPlusTreeNode::NonLeaf(_node) => {
                                            temp_nodes.push(TempNode::NonLeaf {
                                                node: BPlusTreeNonLeafNode::new(
                                                    new_range,
                                                    set_union,
                                                    old_acc + new_acc,
                                                    child_hashes,
                                                    child_ids,
                                                ),
                                                idx,
                                            });
                                            let cur_id = *n
                                                .get_child_id(idx)
                                                .ok_or_else(|| anyhow!("Cannot find child node"))?;
                                            cur_id_opt = Some(cur_id);
                                            break;
                                        }
                                    }
                                }

                                let child_id = child;
                                let child_node = self.get_node(child)?;
                                match child_node.as_ref() {
                                    BPlusTreeNode::Leaf(child_n) => {
                                        if key <= child_n.num {
                                            idx = cur_child_idx;
                                            let (new_leaf_id, new_leaf_hash) = if key == child_n.num
                                            {
                                                c_id = child_id;
                                                update_flag = true;
                                                let leaf_set_union = &child_n.data_set | &set;
                                                let old_leaf_acc = child_n.data_set_acc;
                                                self.write_leaf(
                                                    key,
                                                    leaf_set_union,
                                                    old_leaf_acc + new_acc,
                                                )
                                            } else {
                                                self.write_leaf(key, set, new_acc)
                                            };
                                            temp_nodes.push(TempNode::NonLeaf {
                                                node: BPlusTreeNonLeafNode::new(
                                                    new_range,
                                                    set_union,
                                                    old_acc + new_acc,
                                                    child_hashes,
                                                    child_ids,
                                                ),
                                                idx,
                                            });
                                            temp_nodes.push(TempNode::Leaf {
                                                id: new_leaf_id,
                                                hash: new_leaf_hash,
                                            });
                                            break 'outer;
                                        }
                                    }
                                    BPlusTreeNode::NonLeaf(child_n) => {
                                        if key <= child_n.range.get_high() {
                                            idx = cur_child_idx;
                                            temp_nodes.push(TempNode::NonLeaf {
                                                node: BPlusTreeNonLeafNode::new(
                                                    new_range,
                                                    set_union,
                                                    old_acc + new_acc,
                                                    child_hashes,
                                                    child_ids,
                                                ),
                                                idx,
                                            });
                                            let cur_id = *n
                                                .get_child_id(idx)
                                                .ok_or_else(|| anyhow!("Cannot find child node"))?;
                                            cur_id_opt = Some(cur_id);
                                            break;
                                        } else {
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                None => {
                    let (leaf_id, leaf_hash) = self.write_leaf(key, set, new_acc);
                    temp_nodes.push(TempNode::Leaf {
                        id: leaf_id,
                        hash: leaf_hash,
                    });
                    break 'outer;
                }
            }
        }

        let mut new_root_id = BPlusTreeNodeId::next_id();
        let mut new_root_hash = Digest::zero();
        let mut child_ids: Vec<BPlusTreeNodeId> = Vec::new();
        let mut child_hashes: Vec<Digest> = Vec::new();
        let mut cur_tmp_len = temp_nodes.len();
        let original_tmp_len = temp_nodes.len();

        for node in temp_nodes.into_iter().rev() {
            match node {
                TempNode::Leaf { id, hash } => {
                    child_ids.push(id);
                    child_hashes.push(hash);
                    new_root_id = id;
                    new_root_hash = hash;
                }
                TempNode::NonLeaf { mut node, idx } => {
                    if node.child_ids.is_empty() {
                        insert_flag = true;
                        update_flag = false;
                    }
                    if original_tmp_len - cur_tmp_len == 1 && !update_flag {
                        insert_flag = true;
                    }

                    for i in 0..child_ids.len() {
                        if insert_flag {
                            if update_flag && i == child_ids.len() - 1 {
                                *node
                                    .get_child_id_mut(idx + 1)
                                    .ok_or_else(|| anyhow!("Cannot find child node"))? =
                                    child_ids[i];
                                *node
                                    .get_child_hash_mut(idx + 1)
                                    .ok_or_else(|| anyhow!("Cannot find child node"))? =
                                    child_hashes[i];
                                update_flag = false;
                                continue;
                            }
                            node.child_ids.insert(idx, child_ids[i]);
                            node.child_hashes.insert(idx, child_hashes[i]);
                        } else {
                            *node
                                .get_child_id_mut(idx)
                                .ok_or_else(|| anyhow!("Cannot find child node"))? = child_ids[i];
                            *node
                                .get_child_hash_mut(idx)
                                .ok_or_else(|| anyhow!("Cannot find child node"))? =
                                child_hashes[i];
                        }
                    }
                    child_ids.clear();
                    child_hashes.clear();
                    if node.child_ids.len() <= fanout as usize {
                        let (id, hash) = self.write_non_leaf(node);
                        child_ids.push(id);
                        child_hashes.push(hash);
                        new_root_id = id;
                        new_root_hash = hash;
                        insert_flag = false;
                    } else {
                        insert_flag = true;
                        update_flag = true;
                        let mid = (fanout as f32 / 2_f32).ceil() as usize - 1;
                        let mut old_set: Set = Set::new();
                        let mut old_acc = node.data_set_acc;
                        let mut new_set: Set = Set::new();
                        let mut new_range = node.range;
                        let mut new_ids =
                            SmallVec::<[BPlusTreeNodeId; MAX_INLINE_BTREE_FANOUT]>::new();
                        let mut new_hashes = SmallVec::<[Digest; MAX_INLINE_BTREE_FANOUT]>::new();
                        let mut new_acc = old_acc;

                        let ids = node.child_ids.clone();
                        for i in 0..ids.len() {
                            let n_id = ids[i];
                            let nd = self.get_node(n_id)?;
                            if i <= mid {
                                old_set = &old_set | nd.get_set();
                                if i == mid {
                                    node.range.set_high(nd.get_range().get_high());
                                }
                            } else {
                                if i == mid + 1 {
                                    new_range.set_low(nd.get_range().get_low());
                                }
                                new_range.set_high(nd.get_range().get_high());
                                new_set = &new_set | nd.get_set();
                                new_ids.push(nd.get_node_id());
                                new_hashes.push(nd.get_node_hash());

                                node.child_ids.pop();
                                node.child_hashes.pop();
                                old_acc = old_acc - nd.get_node_acc();
                            }
                        }
                        new_acc = new_acc - old_acc;
                        node.data_set = old_set;
                        node.data_set_acc = old_acc;
                        let new_node = BPlusTreeNonLeafNode::new(
                            new_range, new_set, new_acc, new_hashes, new_ids,
                        );

                        let pot_low = node.range.get_low();
                        let pot_high = new_node.range.get_high();
                        let total_set = &node.data_set | &new_node.data_set;

                        let (old_id, old_hash) = self.write_non_leaf(node);
                        let (new_id, new_hash) = self.write_non_leaf(new_node);
                        child_ids.push(old_id);
                        child_ids.push(new_id);
                        child_hashes.push(old_hash);
                        child_hashes.push(new_hash);

                        if cur_tmp_len == 1 {
                            let mut new_root_child_ids =
                                SmallVec::<[BPlusTreeNodeId; MAX_INLINE_BTREE_FANOUT]>::new();
                            let mut new_root_child_hashes =
                                SmallVec::<[Digest; MAX_INLINE_BTREE_FANOUT]>::new();
                            for i in 0..child_ids.len() {
                                new_root_child_ids.push(child_ids[i]);
                                new_root_child_hashes.push(child_hashes[i]);
                            }
                            let new_root = BPlusTreeNonLeafNode::new(
                                Range::new(pot_low, pot_high),
                                total_set,
                                old_acc + new_acc,
                                new_root_child_hashes,
                                new_root_child_ids,
                            );
                            let (new_rt_id, new_rt_hash) = self.write_non_leaf(new_root);
                            new_root_id = new_rt_id;
                            new_root_hash = new_rt_hash;
                        }
                    }
                }
            }
            cur_tmp_len -= 1;
        }

        self.apply.root.bplus_tree_root_id = Some(new_root_id);
        self.apply.root.bplus_tree_root_hash = new_root_hash;
        self.outdated.insert(c_id);
        for id in self.outdated.drain() {
            self.apply.nodes.remove(&id);
        }

        Ok(())
    }

    pub fn delete(&mut self, key: K, obj_id: ObjId, fanout: u8, pk: &AccPublicKey) -> Result<()> {
        let set = Set::from_single_element(obj_id.0);
        let delta_acc = AccValue::from_set(&set, pk);
        let mut cur_id_opt = self.apply.root.bplus_tree_root_id;

        #[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
        enum TempNode<N: Num> {
            Leaf {
                id: BPlusTreeNodeId,
                hash: Digest,
                is_empty: bool,
            },
            NonLeaf {
                node: BPlusTreeNonLeafNode<N>,
                idx: usize,
            },
        }
        let mut temp_nodes: Vec<TempNode<K>> = Vec::new();

        loop {
            match cur_id_opt {
                Some(id) => {
                    self.outdated.insert(id);
                    let cur_node = self.get_node(id)?;
                    match cur_node.as_ref() {
                        BPlusTreeNode::Leaf(n) => {
                            let set_dif = (&n.data_set) / (&set);
                            let old_acc = n.data_set_acc;
                            if n.num == key {
                                let mut is_empty = false;
                                if set_dif.is_empty() {
                                    is_empty = true;
                                }

                                let (id, hash) = self.write_leaf(key, set_dif, old_acc - delta_acc);
                                if is_empty {
                                    self.outdated.insert(id);
                                }
                                temp_nodes.push(TempNode::Leaf { id, hash, is_empty });
                                break;
                            } else {
                                return Err(anyhow!("key not matched at leaf"));
                            }
                        }
                        BPlusTreeNode::NonLeaf(n) => {
                            if n.range.is_in_range(key) {
                                let set_dif = (&n.data_set) / (&set);
                                let old_acc = n.data_set_acc;
                                let child_ids = n.child_ids.clone();
                                let child_hashes = n.child_hashes.clone();

                                let child_ids_len = &child_ids.len();
                                for i in 0..*child_ids_len {
                                    let child_id = child_ids[i];
                                    let child_node = self.get_node(child_id)?;
                                    match child_node.as_ref() {
                                        BPlusTreeNode::Leaf(node) => {
                                            if node.num == key {
                                                temp_nodes.push(TempNode::NonLeaf {
                                                    node: BPlusTreeNonLeafNode::new(
                                                        n.range,
                                                        set_dif,
                                                        old_acc - delta_acc,
                                                        child_hashes,
                                                        child_ids,
                                                    ),
                                                    idx: i,
                                                });
                                                cur_id_opt = Some(child_id);
                                                break;
                                            } else {
                                                continue;
                                            }
                                        }
                                        BPlusTreeNode::NonLeaf(node) => {
                                            if node.range.is_in_range(key) {
                                                temp_nodes.push(TempNode::NonLeaf {
                                                    node: BPlusTreeNonLeafNode::new(
                                                        n.range,
                                                        set_dif,
                                                        old_acc - delta_acc,
                                                        child_hashes,
                                                        child_ids,
                                                    ),
                                                    idx: i,
                                                });
                                                cur_id_opt = Some(child_id);
                                                break;
                                            } else {
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                return Err(anyhow!("key not in range at non leaf node"));
                            }
                        }
                    }
                }
                None => {
                    bail!("Cannot find node");
                }
            }
        }

        let mut new_root_id = self
            .apply
            .root
            .bplus_tree_root_id
            .context("Previous bplus tree root is none")?;
        let mut new_root_hash = Digest::zero();
        let mut delete_flag = false;
        let mut merge_flag = false;
        let mut cur_tmp_len = temp_nodes.len();
        let mut cur_range = Range::new(key, key);

        for node in temp_nodes.into_iter().rev() {
            match node {
                TempNode::Leaf { id, hash, is_empty } => {
                    if is_empty {
                        delete_flag = true;
                    } else {
                        new_root_id = id;
                        new_root_hash = hash;
                        delete_flag = false;
                    }
                }
                TempNode::NonLeaf { mut node, idx } => {
                    if merge_flag {
                        match node.child_ids.get(idx + 1) {
                            Some(id) => {
                                // has right sib
                                let r_sib = self.get_node(*id)?;
                                match r_sib.as_ref() {
                                    BPlusTreeNode::Leaf(_r_n) => {}
                                    BPlusTreeNode::NonLeaf(r_n) => {
                                        if r_n.child_ids.len()
                                            > (fanout as f32 / 2_f32).ceil() as usize
                                        {
                                            // borrow from right
                                            let mut new_r_n_c_ids = r_n.child_ids.clone();
                                            let mut new_r_n_c_hashes = r_n.child_hashes.clone();

                                            let r_n_higher = r_n.range.get_high();
                                            let r_n_c0_id = r_n.child_ids[0];
                                            let r_n_c0 = self.get_node(r_n_c0_id)?;
                                            let r_n_c0_acc = r_n_c0.as_ref().get_node_acc();
                                            let r_n_c1_id = r_n.child_ids[1];
                                            let r_n_c1 = self.get_node(r_n_c1_id)?;
                                            let new_n_range_higher =
                                                r_n_c0.as_ref().get_range_high();

                                            let new_r_n_lower = r_n_c1.as_ref().get_range_low();
                                            let new_r_n_range =
                                                Range::new(new_r_n_lower, r_n_higher);
                                            let new_r_n_set = &r_n.data_set / r_n_c0.get_set();
                                            let n_new_c_id = new_r_n_c_ids[0];
                                            let n_new_c_hash = new_r_n_c_hashes[0];
                                            new_r_n_c_ids.remove(0);
                                            new_r_n_c_hashes.remove(0);
                                            let new_r_n_acc = r_n.data_set_acc - r_n_c0_acc;

                                            let n_id = new_root_id;
                                            let n = self.get_node(n_id)?;

                                            match n.as_ref() {
                                                BPlusTreeNode::Leaf(_n) => {}
                                                BPlusTreeNode::NonLeaf(n) => {
                                                    let n_l_c_id = n.child_ids[0];
                                                    let n_l_c = self.get_node(n_l_c_id)?;
                                                    let n_lower = n_l_c.as_ref().get_range_low();
                                                    let new_n_range =
                                                        Range::new(n_lower, new_n_range_higher);
                                                    let new_n_set = &n.data_set | r_n_c0.get_set();
                                                    let mut new_n_c_ids = n.child_ids.clone();
                                                    let mut new_n_c_hashes = n.child_hashes.clone();
                                                    new_n_c_ids.push(n_new_c_id);
                                                    new_n_c_hashes.push(n_new_c_hash);
                                                    let new_n_acc = n.data_set_acc + r_n_c0_acc;
                                                    let (new_n_id, new_n_hash) = self
                                                        .write_non_leaf(BPlusTreeNonLeafNode::new(
                                                            new_n_range,
                                                            new_n_set,
                                                            new_n_acc,
                                                            new_n_c_hashes,
                                                            new_n_c_ids,
                                                        ));
                                                    let (new_r_id, new_r_hash) = self
                                                        .write_non_leaf(BPlusTreeNonLeafNode::new(
                                                            new_r_n_range,
                                                            new_r_n_set,
                                                            new_r_n_acc,
                                                            new_r_n_c_hashes,
                                                            new_r_n_c_ids,
                                                        ));
                                                    *node.get_child_id_mut(idx).ok_or_else(
                                                        || anyhow!("Cannot find child node"),
                                                    )? = new_n_id;
                                                    *node.get_child_hash_mut(idx).ok_or_else(
                                                        || anyhow!("Cannot find child node"),
                                                    )? = new_n_hash;
                                                    *node.get_child_id_mut(idx + 1).ok_or_else(
                                                        || anyhow!("Cannot find child node"),
                                                    )? = new_r_id;
                                                    *node
                                                        .get_child_hash_mut(idx + 1)
                                                        .ok_or_else(|| {
                                                            anyhow!("Cannot find child node")
                                                        })? = new_r_hash;
                                                }
                                            }
                                        } else if idx > 0 {
                                            // right cannot lend, has left sib
                                            let id = node
                                                .child_ids
                                                .get(idx - 1)
                                                .ok_or_else(|| anyhow!("Cannot find child id"))?;
                                            let l_n = self.get_node(*id)?;
                                            match l_n.as_ref() {
                                                BPlusTreeNode::Leaf(_l_n) => {}
                                                BPlusTreeNode::NonLeaf(l_n) => {
                                                    if l_n.child_ids.len()
                                                        > (fanout as f32 / 2_f32).ceil() as usize
                                                    {
                                                        // borrow from left
                                                        let mut new_l_n_c_ids =
                                                            l_n.child_ids.clone();
                                                        let mut new_l_n_c_hashes =
                                                            l_n.child_hashes.clone();

                                                        let l_n_lower = l_n.range.get_low();
                                                        let l_n_c_size = l_n.child_ids.len();
                                                        let l_n_c0_inv_id =
                                                            l_n.child_ids[l_n_c_size - 1];
                                                        let l_n_c0_inv =
                                                            self.get_node(l_n_c0_inv_id)?;
                                                        let l_n_c0_inv_acc =
                                                            l_n_c0_inv.as_ref().get_node_acc();
                                                        let l_n_c1_inv_id =
                                                            l_n.child_ids[l_n_c_size - 2];
                                                        let l_n_c1_inv =
                                                            self.get_node(l_n_c1_inv_id)?;
                                                        let new_n_lower =
                                                            l_n_c1_inv.as_ref().get_range_low();
                                                        let new_l_n_higher =
                                                            l_n_c1_inv.as_ref().get_range_high();
                                                        let new_l_n_range =
                                                            Range::new(l_n_lower, new_l_n_higher);
                                                        let new_l_n_set =
                                                            &l_n.data_set / l_n_c0_inv.get_set();
                                                        let n_new_c_id = new_l_n_c_ids
                                                            .pop()
                                                            .ok_or_else(|| {
                                                                anyhow!("Child id vector is empty")
                                                            })?;
                                                        let n_new_c_hash = new_l_n_c_hashes
                                                            .pop()
                                                            .ok_or_else(|| {
                                                            anyhow!("Child hash vector is empty")
                                                        })?;
                                                        let new_l_n_acc =
                                                            l_n.data_set_acc - l_n_c0_inv_acc;

                                                        let n_id = new_root_id;
                                                        let n = self.get_node(n_id)?;
                                                        match n.as_ref() {
                                                            BPlusTreeNode::Leaf(_n) => {}
                                                            BPlusTreeNode::NonLeaf(n) => {
                                                                let n_c_size = n.child_ids.len();
                                                                let n_r_c_id =
                                                                    n.child_ids[n_c_size - 1];
                                                                let n_r_c =
                                                                    self.get_node(n_r_c_id)?;
                                                                let n_higher =
                                                                    n_r_c.as_ref().get_range_high();
                                                                let new_n_range = Range::new(
                                                                    new_n_lower,
                                                                    n_higher,
                                                                );
                                                                let new_n_set = &n.data_set
                                                                    | l_n_c0_inv.get_set();
                                                                let mut new_n_c_ids =
                                                                    n.child_ids.clone();
                                                                let mut new_n_c_hashes =
                                                                    n.child_hashes.clone();
                                                                new_n_c_ids.insert(0, n_new_c_id);
                                                                new_n_c_hashes
                                                                    .insert(0, n_new_c_hash);
                                                                let new_n_acc =
                                                                    n.data_set_acc + l_n_c0_inv_acc;
                                                                let (new_n_id, new_n_hash) = self
                                                                    .write_non_leaf(
                                                                        BPlusTreeNonLeafNode::new(
                                                                            new_n_range,
                                                                            new_n_set,
                                                                            new_n_acc,
                                                                            new_n_c_hashes,
                                                                            new_n_c_ids,
                                                                        ),
                                                                    );
                                                                let (new_l_id, new_l_hash) = self
                                                                    .write_non_leaf(
                                                                        BPlusTreeNonLeafNode::new(
                                                                            new_l_n_range,
                                                                            new_l_n_set,
                                                                            new_l_n_acc,
                                                                            new_l_n_c_hashes,
                                                                            new_l_n_c_ids,
                                                                        ),
                                                                    );
                                                                *node
                                                                        .get_child_id_mut(idx)
                                                                        .ok_or_else(|| anyhow!("Cannot find child node"))? = new_n_id;
                                                                *node
                                                                        .get_child_hash_mut(idx)
                                                                        .ok_or_else(|| anyhow!("Cannot find child node"))?= new_n_hash;
                                                                *node
                                                                    .get_child_id_mut(idx - 1)
                                                                    .ok_or_else(|| {
                                                                    anyhow!(
                                                                        "Cannot find child node"
                                                                    )
                                                                })? = new_l_id;
                                                                *node
                                                                        .get_child_hash_mut(idx - 1)
                                                                        .ok_or_else(|| anyhow!("Cannot find child node"))?= new_l_hash;
                                                            }
                                                        }
                                                    } else {
                                                        // merge right
                                                        let mut r_n_ids = r_n.child_ids.clone();
                                                        let mut r_n_hashes =
                                                            r_n.child_hashes.clone();
                                                        let r_n_acc = r_n.data_set_acc;
                                                        let new_n_higher = r_n.range.get_high();

                                                        let n_id = new_root_id;
                                                        let n = self.get_node(n_id)?;
                                                        match n.as_ref() {
                                                            BPlusTreeNode::Leaf(_n) => {}
                                                            BPlusTreeNode::NonLeaf(n) => {
                                                                let mut new_n_ids =
                                                                    n.child_ids.clone();
                                                                let mut new_n_hashes =
                                                                    n.child_hashes.clone();
                                                                let new_n_lower = n.range.get_low();
                                                                let n_acc = n.data_set_acc;
                                                                let new_n_set =
                                                                    &n.data_set | &r_n.data_set;
                                                                new_n_ids.append(&mut r_n_ids);
                                                                new_n_hashes
                                                                    .append(&mut r_n_hashes);
                                                                let new_n_range = Range::new(
                                                                    new_n_lower,
                                                                    new_n_higher,
                                                                );
                                                                let (new_n_id, new_n_hash) = self
                                                                    .write_non_leaf(
                                                                        BPlusTreeNonLeafNode::new(
                                                                            new_n_range,
                                                                            new_n_set,
                                                                            n_acc + r_n_acc,
                                                                            new_n_hashes,
                                                                            new_n_ids,
                                                                        ),
                                                                    );
                                                                new_root_id = new_n_id;
                                                                *node
                                                                        .get_child_id_mut(idx)
                                                                        .ok_or_else(|| anyhow!("Cannot find child node"))?= new_n_id;
                                                                *node
                                                                        .get_child_hash_mut(idx)
                                                                        .ok_or_else(|| anyhow!("Cannot find child node"))?= new_n_hash;
                                                                node.child_ids.remove(idx + 1);
                                                                node.child_hashes.remove(idx + 1);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            // no left sib, merge right
                                            let mut r_n_ids = r_n.child_ids.clone();
                                            let mut r_n_hashes = r_n.child_hashes.clone();
                                            let r_n_acc = r_n.data_set_acc;
                                            let new_n_higher = r_n.range.get_high();
                                            let n_id = new_root_id;
                                            let n = self.get_node(n_id)?;
                                            match n.as_ref() {
                                                BPlusTreeNode::Leaf(_n) => {}
                                                BPlusTreeNode::NonLeaf(n) => {
                                                    let mut new_n_ids = n.child_ids.clone();
                                                    let mut new_n_hashes = n.child_hashes.clone();
                                                    let new_n_lower = n.range.get_low();
                                                    let n_acc = n.data_set_acc;
                                                    let new_n_set = &n.data_set | &r_n.data_set;
                                                    new_n_ids.append(&mut r_n_ids);
                                                    new_n_hashes.append(&mut r_n_hashes);
                                                    let new_n_range =
                                                        Range::new(new_n_lower, new_n_higher);
                                                    let (new_n_id, new_n_hash) = self
                                                        .write_non_leaf(BPlusTreeNonLeafNode::new(
                                                            new_n_range,
                                                            new_n_set,
                                                            n_acc + r_n_acc,
                                                            new_n_hashes,
                                                            new_n_ids,
                                                        ));
                                                    new_root_id = new_n_id;
                                                    *node.get_child_id_mut(idx).ok_or_else(
                                                        || anyhow!("Cannot find child id"),
                                                    )? = new_n_id;
                                                    *node.get_child_hash_mut(idx).ok_or_else(
                                                        || anyhow!("Cannot find child hash"),
                                                    )? = new_n_hash;
                                                    node.child_ids.remove(idx + 1);
                                                    node.child_hashes.remove(idx + 1);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            None => {
                                // no right sib, must has left sib
                                let l_sib_id = node
                                    .child_ids
                                    .get(idx - 1)
                                    .ok_or_else(|| anyhow!("Cannot find child id"))?;
                                let l_sib = self.get_node(*l_sib_id)?;
                                match l_sib.as_ref() {
                                    BPlusTreeNode::Leaf(_l_n) => {}
                                    BPlusTreeNode::NonLeaf(l_n) => {
                                        let mut new_l_n_c_ids = l_n.child_ids.clone();
                                        let mut new_l_n_c_hashes = l_n.child_hashes.clone();
                                        if l_n.child_ids.len()
                                            > (fanout as f32 / 2_f32).ceil() as usize
                                        {
                                            // borrow from left
                                            let l_n_lower = l_n.range.get_low();
                                            let l_n_c_size = l_n.child_ids.len();
                                            let l_n_c0_inv_id = l_n.child_ids[l_n_c_size - 1];
                                            let l_n_c0_inv = self.get_node(l_n_c0_inv_id)?;
                                            let new_n_low = l_n_c0_inv.as_ref().get_range_low();
                                            let l_n_c0_inv_acc = l_n_c0_inv.as_ref().get_node_acc();
                                            let l_n_c1_inv_id = l_n.child_ids[l_n_c_size - 2];
                                            let l_n_c1_inv = self.get_node(l_n_c1_inv_id)?;
                                            let new_l_n_higher =
                                                l_n_c1_inv.as_ref().get_range_high();
                                            let new_l_n_range =
                                                Range::new(l_n_lower, new_l_n_higher);
                                            let new_l_n_set = &l_n.data_set / l_n_c0_inv.get_set();
                                            let n_new_c_id =
                                                new_l_n_c_ids.pop().ok_or_else(|| {
                                                    anyhow!("Child id vector is empty")
                                                })?;
                                            let n_new_c_hash =
                                                new_l_n_c_hashes.pop().ok_or_else(|| {
                                                    anyhow!("Child hash vector is empty")
                                                })?;
                                            let new_l_n_acc = l_n.data_set_acc - l_n_c0_inv_acc;

                                            let n_id = new_root_id;
                                            let n = self.get_node(n_id)?;
                                            match n.as_ref() {
                                                BPlusTreeNode::Leaf(_n) => {}
                                                BPlusTreeNode::NonLeaf(n) => {
                                                    let n_c_size = n.child_ids.len();
                                                    let n_r_c_id = n.child_ids[n_c_size - 1];
                                                    let n_r_c = self.get_node(n_r_c_id)?;
                                                    let n_higher = n_r_c.as_ref().get_range_high();
                                                    let new_n_range =
                                                        Range::new(new_n_low, n_higher);
                                                    let new_n_set =
                                                        &n.data_set | l_n_c0_inv.get_set();
                                                    let mut new_n_c_ids = n.child_ids.clone();
                                                    let mut new_n_c_hashes = n.child_hashes.clone();
                                                    new_n_c_ids.insert(0, n_new_c_id);
                                                    new_n_c_hashes.insert(0, n_new_c_hash);
                                                    let new_n_acc = n.data_set_acc + l_n_c0_inv_acc;
                                                    let (new_n_id, new_n_hash) = self
                                                        .write_non_leaf(BPlusTreeNonLeafNode::new(
                                                            new_n_range,
                                                            new_n_set,
                                                            new_n_acc,
                                                            new_n_c_hashes,
                                                            new_n_c_ids,
                                                        ));
                                                    let (new_l_id, new_l_hash) = self
                                                        .write_non_leaf(BPlusTreeNonLeafNode::new(
                                                            new_l_n_range,
                                                            new_l_n_set,
                                                            new_l_n_acc,
                                                            new_l_n_c_hashes,
                                                            new_l_n_c_ids,
                                                        ));
                                                    *node.get_child_id_mut(idx).ok_or_else(
                                                        || anyhow!("Cannot find child id"),
                                                    )? = new_n_id;
                                                    *node.get_child_hash_mut(idx).ok_or_else(
                                                        || anyhow!("Cannot find child hash"),
                                                    )? = new_n_hash;
                                                    *node.get_child_id_mut(idx - 1).ok_or_else(
                                                        || anyhow!("Cannot find child id"),
                                                    )? = new_l_id;
                                                    *node
                                                        .get_child_hash_mut(idx - 1)
                                                        .ok_or_else(|| {
                                                            anyhow!("Cannot find child hash")
                                                        })? = new_l_hash;
                                                }
                                            }
                                        } else {
                                            // merge left
                                            let l_n_acc = l_n.data_set_acc;
                                            let new_n_lower = l_n.range.get_low();
                                            let n_id = new_root_id;
                                            let n = self.get_node(n_id)?;
                                            match n.as_ref() {
                                                BPlusTreeNode::Leaf(_n) => {}
                                                BPlusTreeNode::NonLeaf(n) => {
                                                    let mut new_n_ids = n.child_ids.clone();
                                                    let mut new_n_hashes = n.child_hashes.clone();

                                                    let n_c_size = n.child_ids.len();
                                                    let n_r_c_id = n.child_ids[n_c_size - 1];
                                                    let n_r_c = self.get_node(n_r_c_id)?;
                                                    let n_higher = n_r_c.as_ref().get_range_high();

                                                    let n_acc = n.data_set_acc;
                                                    let new_n_set = &n.data_set | &l_n.data_set;
                                                    new_l_n_c_ids.append(&mut new_n_ids);
                                                    new_l_n_c_hashes.append(&mut new_n_hashes);
                                                    let new_n_range =
                                                        Range::new(new_n_lower, n_higher);
                                                    let (new_n_id, new_n_hash) = self
                                                        .write_non_leaf(BPlusTreeNonLeafNode::new(
                                                            new_n_range,
                                                            new_n_set,
                                                            n_acc + l_n_acc,
                                                            new_l_n_c_hashes,
                                                            new_l_n_c_ids,
                                                        ));
                                                    new_root_id = new_n_id;
                                                    *node.get_child_id_mut(idx).ok_or_else(
                                                        || anyhow!("Cannot find child id"),
                                                    )? = new_n_id;
                                                    *node.get_child_hash_mut(idx).ok_or_else(
                                                        || anyhow!("Cannot find child hash"),
                                                    )? = new_n_hash;
                                                    node.child_ids.remove(idx - 1);
                                                    node.child_hashes.remove(idx - 1);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else if delete_flag {
                        node.child_ids.remove(idx);
                        node.child_hashes.remove(idx);
                        if key == node.range.get_low() {
                            let sib_id = node.child_ids[0];
                            let sib_n = self.get_node(sib_id)?;
                            match sib_n.as_ref() {
                                BPlusTreeNode::Leaf(sib) => {
                                    node.range.set_low(sib.num);
                                }
                                BPlusTreeNode::NonLeaf(sib) => {
                                    node.range.set_low(sib.range.get_low());
                                }
                            }
                        } else if key == node.range.get_high() {
                            let children_size = node.child_ids.len();
                            let sib_id = node.child_ids[children_size - 1];
                            let sib_n = self.get_node(sib_id)?;
                            match sib_n.as_ref() {
                                BPlusTreeNode::Leaf(sib) => {
                                    node.range.set_high(sib.num);
                                }
                                BPlusTreeNode::NonLeaf(sib) => {
                                    node.range.set_high(sib.range.get_high());
                                }
                            }
                        }
                        cur_range = node.range;
                    } else {
                        if key == node.range.get_low() {
                            node.range.set_low(cur_range.get_low());
                        } else if key == node.range.get_high() {
                            node.range.set_high(cur_range.get_high());
                        }
                        *node
                            .get_child_id_mut(idx)
                            .ok_or_else(|| anyhow!("Cannot find child id"))? = new_root_id;
                        *node
                            .get_child_hash_mut(idx)
                            .ok_or_else(|| anyhow!("Cannot find child hash"))? = new_root_hash;
                        let (id, hash) = self.write_non_leaf(node);
                        new_root_id = id;
                        new_root_hash = hash;
                        continue;
                    }

                    if node.child_ids.len() < (fanout as f32 / 2_f32).ceil() as usize {
                        if cur_tmp_len == 1 {
                            merge_flag = false;
                            if node.child_ids.len() == 1 {
                                if delete_flag {
                                    let child_id = node.child_ids[0];
                                    let child_n = self.get_node(child_id)?;
                                    new_root_id = child_id;
                                    new_root_hash = child_n.as_ref().to_digest();
                                }
                                break;
                            } else {
                                let (id, hash) = self.write_non_leaf(node);
                                new_root_id = id;
                                new_root_hash = hash;
                            }
                        } else {
                            merge_flag = true;
                            let (id, hash) = self.write_non_leaf(node);
                            new_root_id = id;
                            new_root_hash = hash;
                            self.outdated.insert(new_root_id);
                        }
                    } else {
                        if key == node.range.get_low() {
                            let sib_id = node.child_ids[0];
                            let sib_n = self.get_node(sib_id)?;
                            match sib_n.as_ref() {
                                BPlusTreeNode::Leaf(sib) => {
                                    node.range.set_low(sib.num);
                                }
                                BPlusTreeNode::NonLeaf(sib) => {
                                    node.range.set_low(sib.range.get_low());
                                }
                            }
                        } else if key == node.range.get_high() {
                            let children_size = node.child_ids.len();
                            let sib_id = node.child_ids[children_size - 1];
                            let sib_n = self.get_node(sib_id)?;
                            match sib_n.as_ref() {
                                BPlusTreeNode::Leaf(sib) => {
                                    node.range.set_high(sib.num);
                                }
                                BPlusTreeNode::NonLeaf(sib) => {
                                    node.range.set_high(sib.range.get_high());
                                }
                            }
                        }
                        cur_range = node.range;
                        let (id, hash) = self.write_non_leaf(node);
                        new_root_id = id;
                        new_root_hash = hash;
                        merge_flag = false;
                    }
                    delete_flag = false;
                }
            }
            cur_tmp_len -= 1;
        }

        self.apply.root.bplus_tree_root_id = Some(new_root_id);
        self.apply.root.bplus_tree_root_hash = new_root_hash;
        for id in self.outdated.drain() {
            self.apply.nodes.remove(&id);
        }
        Ok(())
    }
}
