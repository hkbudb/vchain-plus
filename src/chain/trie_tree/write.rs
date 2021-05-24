use super::{
    split_at_common_prefix2, AccValue, Digest, Digestible, Set, TrieLeafNode, TrieNode, TrieNodeId,
    TrieNodeLoader, TrieNonLeafNode,
};
use crate::{
    chain::{id_tree::IdTreeObjId},
    set,
    acc::AccPublicKey,
};
use anyhow::{anyhow, Result};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Apply {
    pub root_id: TrieNodeId,
    pub nodes: HashMap<TrieNodeId, TrieNode>,
}

pub struct WriteContext<L: TrieNodeLoader> {
    node_loader: L,
    apply: Apply,
    outdated: HashSet<TrieNodeId>,
}

impl<L: TrieNodeLoader> WriteContext<L> {
    pub fn new(node_loader: L, root_id: TrieNodeId) -> Self {
        Self {
            node_loader,
            apply: Apply {
                root_id,
                nodes: HashMap::new(),
            },
            outdated: HashSet::new(),
        }
    }

    pub fn changes(self) -> Apply {
        self.apply
    }

    pub fn write_leaf(
        &mut self,
        rest: String,
        data_set: Set,
        acc: AccValue,
    ) -> (TrieNodeId, Digest) {
        let n = TrieLeafNode::new(rest, data_set, acc);
        let id = n.id;
        let hash = n.to_digest();
        self.apply.nodes.insert(id, TrieNode::from_leaf(n));
        (id, hash)
    }

    pub fn write_non_leaf(&mut self, n: TrieNonLeafNode) -> (TrieNodeId, Digest) {
        let id = n.id;
        let hash = n.to_digest();
        self.apply.nodes.insert(id, TrieNode::from_non_leaf(n));
        (id, hash)
    }

    fn get_node(&self, id: TrieNodeId) -> Result<Option<Cow<TrieNode>>> {
        Ok(match self.apply.nodes.get(&id) {
            Some(n) => Some(Cow::Borrowed(n)),
            None => self.node_loader.load_node(id)?.map(Cow::Owned),
        })
    }

    pub fn insert(&mut self, key: String, obj_id: IdTreeObjId, pk: &AccPublicKey) -> Result<()> {
        let set = match obj_id {
            IdTreeObjId(id) => {
                set! {id}
            }
        };
        let new_acc = AccValue::from_set(&set, pk);
        let mut cur_id = self.apply.root_id;
        let mut cur_key = key;

        enum TempNode {
            Leaf { id: TrieNodeId, hash: Digest },
            NonLeaf { node: TrieNonLeafNode, idx: char },
        }
        let mut temp_nodes: Vec<TempNode> = Vec::new();

        loop {
            self.outdated.insert(cur_id);
            let cur_node = match self.get_node(cur_id)? {
                Some(n) => n,
                None => {
                    let (leaf_id, leaf_hash) = self.write_leaf(cur_key, set, new_acc);
                    temp_nodes.push(TempNode::Leaf {
                        id: leaf_id,
                        hash: leaf_hash,
                    });
                    break;
                }
            };

            match cur_node.as_ref() {
                TrieNode::Leaf(n) => {
                    if cur_key == n.rest {
                        let leaf_set = &set | &n.data_set;
                        let sets_inter = (&set) & (&n.data_set);
                        let leaf_acc =
                            new_acc + n.data_set_acc - AccValue::from_set(&sets_inter, pk);
                        let (leaf_id, leaf_hash) = self.write_leaf(cur_key, leaf_set, leaf_acc);
                        temp_nodes.push(TempNode::Leaf {
                            id: leaf_id,
                            hash: leaf_hash,
                        });
                        break;
                    } else {
                        let (common_key, cur_idx, rest_cur_key, node_idx, rest_node_key) =
                            split_at_common_prefix2(&cur_key, &n.rest);
                        let non_leaf_set = &set | &n.data_set;
                        let sets_inter = (&set) & (&n.data_set);
                        let non_leaf_acc =
                            new_acc + n.data_set_acc - AccValue::from_set(&sets_inter, pk);
                        let node_data_set = n.data_set.clone();
                        let node_acc = n.data_set_acc;
                        let (node_leaf_id, node_leaf_hash) =
                            self.write_leaf(rest_node_key, node_data_set, node_acc);

                        let mut btree_map: BTreeMap<char, (TrieNodeId, Digest)> = BTreeMap::new();
                        btree_map.insert(node_idx, (node_leaf_id, node_leaf_hash));
                        let non_leaf =
                            TrieNonLeafNode::new(common_key, non_leaf_set, non_leaf_acc, btree_map);
                        temp_nodes.push(TempNode::NonLeaf {
                            node: non_leaf,
                            idx: cur_idx,
                        });

                        let (leaf_id, leaf_hash) = self.write_leaf(rest_cur_key, set, new_acc);
                        temp_nodes.push(TempNode::Leaf {
                            id: leaf_id,
                            hash: leaf_hash,
                        });
                        break;
                    }
                }
                TrieNode::NonLeaf(n) => {
                    let (common_key, cur_idx, rest_cur_key, node_idx, rest_node_key) =
                        split_at_common_prefix2(&cur_key, &n.nibble);
                    let non_leaf_set = &set | &n.data_set;
                    let sets_inter = (&set) & (&n.data_set);
                    let non_leaf_acc =
                        new_acc + n.data_set_acc - AccValue::from_set(&sets_inter, pk);
                    if common_key == n.nibble {
                        match n.children.get(&cur_idx) {
                            Some((id, _digest)) => {
                                // has path, go down
                                temp_nodes.push(TempNode::NonLeaf {
                                    node: TrieNonLeafNode::new(
                                        common_key,
                                        non_leaf_set,
                                        non_leaf_acc,
                                        n.children.clone(),
                                    ),
                                    idx: cur_idx,
                                });
                                cur_id = *id;
                                cur_key = rest_cur_key;
                            }
                            None => {
                                // no path, create leaf
                                let non_leaf = TrieNonLeafNode::new(
                                    common_key,
                                    non_leaf_set,
                                    non_leaf_acc,
                                    n.children.clone(),
                                );
                                let (new_leaf_id, new_leaf_hash) =
                                    self.write_leaf(rest_cur_key, set, new_acc);
                                temp_nodes.push(TempNode::NonLeaf {
                                    node: non_leaf,
                                    idx: cur_idx,
                                });
                                temp_nodes.push(TempNode::Leaf {
                                    id: new_leaf_id,
                                    hash: new_leaf_hash,
                                });
                                break;
                            }
                        }
                    } else {
                        let mut btree_map: BTreeMap<char, (TrieNodeId, Digest)> = BTreeMap::new();

                        let child_non_leaf = TrieNonLeafNode::new(
                            rest_node_key,
                            n.data_set.clone(),
                            n.data_set_acc,
                            n.children.clone(),
                        );
                        let (child_non_leaf_id, child_non_leaf_hash) =
                            self.write_non_leaf(child_non_leaf);
                        btree_map.insert(node_idx, (child_non_leaf_id, child_non_leaf_hash));

                        let (new_leaf_id, new_leaf_hash) =
                            self.write_leaf(rest_cur_key, set, new_acc);
                        let non_leaf =
                            TrieNonLeafNode::new(common_key, non_leaf_set, non_leaf_acc, btree_map);
                        temp_nodes.push(TempNode::NonLeaf {
                            node: non_leaf,
                            idx: cur_idx,
                        });
                        temp_nodes.push(TempNode::Leaf {
                            id: new_leaf_id,
                            hash: new_leaf_hash,
                        });
                        break;
                    }
                }
            }
        }

        let mut new_root_id = TrieNodeId::next_id();
        let mut new_root_hash = Digest::zero();

        for node in temp_nodes.into_iter().rev() {
            match node {
                TempNode::Leaf { id, hash } => {
                    new_root_id = id;
                    new_root_hash = hash;
                }
                TempNode::NonLeaf { mut node, idx } => {
                    node.children.insert(idx, (new_root_id, new_root_hash));
                    let (id, hash) = self.write_non_leaf(node);
                    new_root_id = id;
                    new_root_hash = hash;
                }
            }
        }
        self.apply.root_id = new_root_id;
        for id in self.outdated.drain() {
            self.apply.nodes.remove(&id);
        }

        Ok(())
    }

    pub fn delete(&mut self, key: String, obj_id: IdTreeObjId, pk: &AccPublicKey) -> Result<()> {
        let set = match obj_id {
            IdTreeObjId(id) => {
                set! {id}
            }
        };
        let delta_acc = AccValue::from_set(&set, pk);
        let mut cur_id = self.apply.root_id;
        let mut cur_key = key;

        enum TempNode {
            Leaf {
                id: TrieNodeId,
                hash: Digest,
                is_empty: bool,
            },
            NonLeaf {
                node: TrieNonLeafNode,
                idx: char,
            },
        }
        let mut temp_nodes: Vec<TempNode> = Vec::new();

        loop {
            self.outdated.insert(cur_id);
            let cur_node = self
                .get_node(cur_id)?
                .ok_or_else(|| anyhow!("Cannot find node!"))?;

            match cur_node.as_ref() {
                TrieNode::Leaf(n) => {
                    if cur_key == n.rest {
                        let set_dif = (&n.data_set) / (&set);
                        let old_acc = n.data_set_acc;
                        let mut is_empty = false;
                        if set_dif.is_empty() {
                            is_empty = true;
                        }
                        let (id, hash) = self.write_leaf(cur_key, set_dif, old_acc - delta_acc);
                        if is_empty {
                            self.outdated.insert(id);
                        }
                        temp_nodes.push(TempNode::Leaf { id, hash, is_empty });
                        break;
                    } else {
                        return Err(anyhow!("Key not found"));
                    }
                }
                TrieNode::NonLeaf(n) => {
                    let (_common_key, cur_idx, rest_cur_key, _node_idx, _rest_node_key) =
                        split_at_common_prefix2(&cur_key, &n.nibble);
                    match n.children.get(&cur_idx) {
                        Some((id, _hash)) => {
                            let set_dif = (&n.data_set) / (&set);
                            let old_acc = n.data_set_acc;
                            let non_leaf = TrieNonLeafNode::new(
                                n.nibble.clone(),
                                set_dif,
                                old_acc - delta_acc,
                                n.children.clone(),
                            );
                            temp_nodes.push(TempNode::NonLeaf {
                                node: non_leaf,
                                idx: cur_idx,
                            });
                            cur_id = *id;
                            cur_key = rest_cur_key;
                        }
                        None => {
                            return Err(anyhow!("Key not found"));
                        }
                    }
                }
            }
        }

        let mut new_root_id = TrieNodeId::next_id();
        let mut new_root_hash = Digest::zero();
        let mut empty_flag = false;

        for node in temp_nodes.into_iter().rev() {
            match node {
                TempNode::Leaf { id, hash, is_empty } => {
                    new_root_id = id;
                    new_root_hash = hash;
                    empty_flag = is_empty;
                }
                TempNode::NonLeaf { mut node, idx } => {
                    if empty_flag {
                        node.children.remove(&idx);
                    } else {
                        node.children.insert(idx, (new_root_id, new_root_hash));
                    }

                    if node.children.len() == 1 {
                        empty_flag = false;
                        let mut new_str: String = node.nibble;
                        for (c, (id, _hash)) in node.children {
                            self.outdated.insert(id);
                            let child_n = self
                                .get_node(id)?
                                .ok_or_else(|| anyhow!("Cannot find node!"))?;
                            match child_n.as_ref() {
                                TrieNode::Leaf(n) => {
                                    if c == '\0' {
                                        new_str.push_str(&n.rest);
                                    } else {
                                        new_str.push(c);
                                        new_str.push_str(&n.rest);
                                    }
                                    let new_set = n.data_set.clone();
                                    let new_acc = n.data_set_acc;
                                    let (new_id, new_hash) =
                                        self.write_leaf(new_str.clone(), new_set, new_acc);
                                    new_root_id = new_id;
                                    new_root_hash = new_hash;
                                }
                                TrieNode::NonLeaf(n) => {
                                    if c == '\0' {
                                        new_str.push_str(&n.nibble);
                                    } else {
                                        new_str.push(c);
                                        new_str.push_str(&n.nibble);
                                    }
                                    let new_non_leaf = TrieNonLeafNode::new(
                                        new_str.clone(),
                                        n.data_set.clone(),
                                        n.data_set_acc,
                                        n.children.clone(),
                                    );
                                    let (new_id, new_hash) = self.write_non_leaf(new_non_leaf);
                                    new_root_id = new_id;
                                    new_root_hash = new_hash;
                                }
                            }
                        }
                    } else {
                        if node.children.is_empty() {
                            empty_flag = true;
                        } else {
                            empty_flag = false;
                        }

                        let (id, hash) = self.write_non_leaf(node);
                        if empty_flag {
                            self.outdated.insert(id);
                        }

                        new_root_id = id;
                        new_root_hash = hash;
                    }
                }
            }
        }

        self.apply.root_id = new_root_id;
        for id in self.outdated.drain() {
            self.apply.nodes.remove(&id);
        }

        Ok(())
    }
}
