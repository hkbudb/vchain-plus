use crate::{
    acc::set::Set,
    chain::{range::Range, traits::Num, DEFAULT_IDX, MAX_FANOUT},
};

use super::{
    BPlusTreeLeafNode, BPlusTreeNode, BPlusTreeNodeId, BPlusTreeNodeLoader, BPlusTreeNonLeafNode,
    Digest, Digestible,
};
use anyhow::Result;
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Apply<K: Num> {
    pub root_id: BPlusTreeNodeId,
    pub nodes: HashMap<BPlusTreeNodeId, BPlusTreeNode<K>>,
}

pub struct WriteContext<K: Num, L: BPlusTreeNodeLoader<K>> {
    node_loader: L,
    apply: Apply<K>,
    outdated: HashSet<BPlusTreeNodeId>,
}

impl<K: Num, L: BPlusTreeNodeLoader<K>> WriteContext<K, L> {
    pub fn new(node_loader: L, root_id: BPlusTreeNodeId) -> Self {
        Self {
            node_loader,
            apply: Apply {
                root_id: root_id,
                nodes: HashMap::new(),
            },
            outdated: HashSet::new(),
        }
    }

    pub fn changes(self) -> Apply<K> {
        self.apply
    }

    pub fn write_leaf(&mut self, num: K, data_set: Set) -> (BPlusTreeNodeId, Digest) {
        let node = BPlusTreeLeafNode::new(num, data_set);
        let id = node.id;
        let hash = node.to_digest();
        self.apply.nodes.insert(id, BPlusTreeNode::from_leaf(node));
        (id, hash)
    }

    pub fn write_non_leaf(&mut self, n: BPlusTreeNonLeafNode<K>) -> (BPlusTreeNodeId, Digest) {
        let id = n.id;
        let hash = n.to_digest();
        self.apply.nodes.insert(id, BPlusTreeNode::from_non_leaf(n));
        (id, hash)
    }

    fn get_node(&self, id: BPlusTreeNodeId) -> Result<Option<Cow<BPlusTreeNode<K>>>> {
        Ok(match self.apply.nodes.get(&id) {
            Some(n) => Some(Cow::Borrowed(n)),
            None => {
                let res = self.node_loader.load_node(id)?.map(Cow::Owned);
                res
            }
        })
    }

    pub fn insert(&mut self, key: K, set: Set) -> Result<()> {
        println!("inserting key {:?}", key);
        let mut cur_id = self.apply.root_id;

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

        'outer: loop {
            self.outdated.insert(cur_id);
            let cur_node = match self.get_node(cur_id)? {
                Some(mut n) => n,
                None => {
                    let (leaf_id, leaf_hash) = self.write_leaf(key, set);
                    temp_nodes.push(TempNode::Leaf {
                        id: leaf_id,
                        hash: leaf_hash,
                    });
                    break 'outer;
                }
            };

            match cur_node.as_ref() {
                BPlusTreeNode::Leaf(n) => {
                    // only when the root is leaf can this condition reached
                    let set_union = &n.data_set | &set;
                    let old_num = n.num;
                    let old_data_set = n.data_set.clone();

                    let new_range: Range<K>;
                    if old_num < key {
                        new_range = Range::new(old_num, key);
                    } else {
                        new_range = Range::new(key, old_num);
                    }
                    let non_leaf = BPlusTreeNonLeafNode::new(
                        new_range, // range may not correct, order and bound
                        set_union,
                        SmallVec::<[Digest; MAX_FANOUT]>::new(),
                        SmallVec::<[BPlusTreeNodeId; MAX_FANOUT]>::new(),
                    );
                    temp_nodes.push(TempNode::NonLeaf {
                        node: non_leaf,
                        idx: 0,
                    });
                    let (old_leaf_id, old_leaf_hash) = self.write_leaf(old_num, old_data_set);
                    let (new_leaf_id, new_leaf_hash) = self.write_leaf(key, set.clone());
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
                    let mut right_flag = false;
                    let new_range: Range<K>;
                    if n.range.is_in_range(key) {
                        new_range = n.range;
                    } else {
                        if key < n.range.get_low() {
                            new_range = Range::new(key, n.range.get_high());
                        } else {
                            new_range = Range::new(n.range.get_low(), key);
                            right_flag = true;
                            // todo here upper bound should be key+1 since range means [l, h)
                        }
                    }

                    let mut idx: usize = 0;
                    let mut cur_child_idx: usize = 0;
                    let child_len: usize = child_ids.len();

                    for child in child_ids.clone() {
                        if right_flag {
                            idx = child_len - 1;  // pos of the last child
                            let child_node = self.get_node(child).unwrap().unwrap();
                            match child_node.as_ref() {
                                BPlusTreeNode::Leaf(node) => {
                                    temp_nodes.push(TempNode::NonLeaf {
                                        node: BPlusTreeNonLeafNode::new(
                                            new_range,
                                            set_union,
                                            child_hashes,
                                            child_ids,
                                        ),
                                        idx: idx + 1,
                                    });
                                    let (new_id, new_hash) = self.write_leaf(key, set);
                                    temp_nodes.push(TempNode::Leaf {
                                        id: new_id,
                                        hash: new_hash,
                                    });
                                    break 'outer;
                                }
                                BPlusTreeNode::NonLeaf(node) => {
                                    temp_nodes.push(TempNode::NonLeaf {
                                        node: BPlusTreeNonLeafNode::new(
                                            new_range,
                                            set_union,
                                            child_hashes,
                                            child_ids,
                                        ),
                                        idx: idx,
                                    });
                                    cur_id = *n.get_child_id(idx).unwrap();
                                    break;
                                }
                            }
                        }

                        let child_node = self.get_node(child).unwrap().unwrap();
                        match child_node.as_ref() {
                            BPlusTreeNode::Leaf(child_n) => {
                                if key < child_n.num {
                                    idx = cur_child_idx;
                                    let (new_id, new_hash) = self.write_leaf(key, set.clone());
                                    temp_nodes.push(TempNode::NonLeaf {
                                        node: BPlusTreeNonLeafNode::new(
                                            new_range,
                                            set_union,
                                            child_hashes,
                                            child_ids,
                                        ),
                                        idx: idx,
                                    });
                                    temp_nodes.push(TempNode::Leaf {
                                        id: new_id,
                                        hash: new_hash,
                                    });
                                    break 'outer;
                                }
                            }
                            BPlusTreeNode::NonLeaf(child_n) => {
                                if key < child_n.range.get_high() {
                                    idx = cur_child_idx;
                                    temp_nodes.push(TempNode::NonLeaf {
                                        node: BPlusTreeNonLeafNode::new(
                                            new_range,
                                            set_union,
                                            child_hashes,
                                            child_ids,
                                        ),
                                        idx: idx,
                                    });
                                    cur_id = *n.get_child_id(idx).unwrap();
                                    // if cur_child_idx == child_len - 1 {
                                    //     cur_id = *n.get_child_id(idx).unwrap();
                                    // } else {
                                    //     cur_id = *n.get_child_id(idx-1).unwrap();
                                    // }
                                    break;
                                }
                            }
                        }
                        cur_child_idx += 1;
                    }
                }
            }
        }

        let mut new_root_id = BPlusTreeNodeId::next_id();
        let mut new_root_hash = Digest::zero();
        let mut child_ids: Vec<BPlusTreeNodeId> = Vec::new();
        let mut child_hashes: Vec<Digest> = Vec::new();
        let mut cur_tmp_len = temp_nodes.len();
        let original_tmp_len = temp_nodes.len();
        //println!("{:#?}", temp_nodes);
        let mut insert_flag = false;
        let mut update_flag = false;
        for node in temp_nodes.into_iter().rev() {
            match node {
                TempNode::Leaf { id, hash } => {
                    child_ids.push(id);
                    child_hashes.push(hash);
                    new_root_id = id;
                    new_root_hash = hash;
                }
                TempNode::NonLeaf { mut node, idx } => {
                    // match node.get_child_id(idx) {
                    //     None => {
                    //         println!("insert due to none");
                    //         insert_flag = true;
                    //         if node.child_ids.len() > 0 {
                    //             println!("update due to none & child len > 0");
                    //             insert_flag = false;
                    //         }
                    //     },
                    //     Some(id) => {
                    //         println!("update due to not none");
                    //         insert_flag = false;
                    //     },
                    // }
                    if node.child_ids.len() == 0 {
                        // special case: second insertion
                        //println!("insert due to second insertion");
                        insert_flag = true;
                        update_flag = false;
                    }
                    if original_tmp_len - cur_tmp_len == 1 {
                        insert_flag = true;
                        //println!("insert due to level 2");
                    }

                    for i in 0..child_ids.len() {
                        if insert_flag {
                            if update_flag && i == child_ids.len() - 1 {
                                *node.get_child_id_mut(idx + 1).unwrap() = child_ids[i];
                                *node.get_child_hash_mut(idx + 1).unwrap() = child_hashes[i];
                                update_flag = false;
                                continue;
                            }
                            node.child_ids.insert(idx, child_ids[i]);
                            node.child_hashes.insert(idx, child_hashes[i]);
                        } else {
                            *node.get_child_id_mut(idx).unwrap() = child_ids[i];
                            *node.get_child_hash_mut(idx).unwrap() = child_hashes[i];
                        }
                    }
                    child_ids.clear();
                    child_hashes.clear();
                    if node.child_ids.len() <= MAX_FANOUT {
                        let (id, hash) = self.write_non_leaf(node);
                        child_ids.push(id);
                        child_hashes.push(hash);
                        new_root_id = id;
                        new_root_hash = hash;
                        insert_flag = false;
                    } else {
                        // split
                        insert_flag = true;
                        update_flag = true;
                        let mid = (MAX_FANOUT as f32 / 2 as f32).ceil() as usize - 1;
                        let mut old_set: Set = Set::new();
                        let mut new_set: Set = Set::new();
                        let mut new_range = node.range;
                        let mut new_ids = SmallVec::<[BPlusTreeNodeId; MAX_FANOUT]>::new();
                        let mut new_hashes = SmallVec::<[Digest; MAX_FANOUT]>::new();

                        let ids = node.child_ids.clone();
                        let hashes = node.child_hashes.clone();
                        for i in 0..ids.len() {
                            let n_id = ids[i];
                            let nd = self.get_node(n_id).unwrap().unwrap();

                            if i <= mid {
                                // old
                                old_set = &old_set | &nd.get_set();
                                if i == mid {
                                    node.range.set_high(nd.get_range().get_high());
                                }
                            } else {
                                // new
                                if i == mid + 1 {
                                    new_range.set_low(nd.get_range().get_low());
                                }
                                new_range.set_high(nd.get_range().get_high());
                                new_set = &new_set | &nd.get_set();
                                new_ids.push(nd.get_node_id());
                                new_hashes.push(nd.get_node_hash());

                                node.child_ids.pop();
                                node.child_hashes.pop();
                            }
                        }
                        node.data_set = old_set;
                        let new_node =
                            BPlusTreeNonLeafNode::new(new_range, new_set, new_hashes, new_ids);

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
                            // the node is in the top now, need to create a new root
                            let mut new_root_child_ids =
                                SmallVec::<[BPlusTreeNodeId; MAX_FANOUT]>::new();
                            let mut new_root_child_hashes = SmallVec::<[Digest; MAX_FANOUT]>::new();
                            for i in 0..child_ids.len() {
                                new_root_child_ids.push(child_ids[i]);
                                new_root_child_hashes.push(child_hashes[i]);
                                //new_root_child_ids.insert(0, child_ids[i]);
                                //new_root_child_hashes.insert(0, child_hashes[i]);
                            }
                            let new_root = BPlusTreeNonLeafNode::new(
                                Range::new(pot_low, pot_high),
                                total_set,
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

        self.apply.root_id = new_root_id;

        for id in self.outdated.drain() {
            self.apply.nodes.remove(&id);
        }

        Ok(())
    }
}
