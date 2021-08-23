use crate::acc::AccPublicKey;
use crate::chain::{
    id_tree::ObjId,
    trie_tree::{
        split_at_common_prefix2, AccValue, Digest, Digestible, Set, TrieLeafNode, TrieNode,
        TrieNodeId, TrieNodeLoader, TrieNonLeafNode, TrieRoot,
    },
};
use anyhow::{anyhow, bail, Result};
use serde::{Deserialize, Serialize};
use smol_str::SmolStr;
use std::collections::BTreeMap;
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Apply {
    pub root: TrieRoot,
    pub nodes: HashMap<TrieNodeId, TrieNode>,
}

#[derive(Debug, Clone)]
pub struct WriteContext<'a, L: TrieNodeLoader> {
    node_loader: &'a L,
    apply: Apply,
    outdated: HashSet<TrieNodeId>,
}

impl<'a, L: TrieNodeLoader> WriteContext<'a, L> {
    pub fn new(node_loader: &'a L, root: TrieRoot) -> Self {
        Self {
            node_loader,
            apply: Apply {
                root,
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
        rest: SmolStr,
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

    fn get_node(&self, id: TrieNodeId) -> Result<Cow<TrieNode>> {
        Ok(match self.apply.nodes.get(&id) {
            Some(n) => Cow::Borrowed(n),
            None => Cow::Owned(self.node_loader.load_node(id)?),
        })
    }

    pub fn insert(&mut self, key: SmolStr, obj_id: ObjId, pk: &AccPublicKey) -> Result<()> {
        let set = Set::from_single_element(obj_id.0);
        let new_acc = AccValue::from_set(&set, pk);
        let mut cur_id_opt = self.apply.root.trie_root_id;
        let mut cur_key = key;

        #[allow(clippy::large_enum_variant)]
        enum TempNode {
            Leaf { id: TrieNodeId, hash: Digest },
            NonLeaf { node: TrieNonLeafNode, idx: char },
        }
        let mut temp_nodes: Vec<TempNode> = Vec::new();

        loop {
            match cur_id_opt {
                Some(id) => {
                    self.outdated.insert(id);
                    let cur_node = self.get_node(id)?;
                    match cur_node.as_ref() {
                        TrieNode::Leaf(n) => {
                            if cur_key == n.rest {
                                let leaf_set = &set | &n.data_set;
                                let sets_inter = (&set) & (&n.data_set);
                                let leaf_acc =
                                    new_acc + n.data_set_acc - AccValue::from_set(&sets_inter, pk);
                                let (leaf_id, leaf_hash) =
                                    self.write_leaf(cur_key, leaf_set, leaf_acc);
                                temp_nodes.push(TempNode::Leaf {
                                    id: leaf_id,
                                    hash: leaf_hash,
                                });
                            } else {
                                let (common_key, cur_idx, rest_cur_key, node_idx, rest_node_key) =
                                    split_at_common_prefix2(&cur_key, &n.rest);
                                let non_leaf_set = &set | &n.data_set;
                                let sets_inter = (&set) & (&n.data_set);
                                let non_leaf_acc =
                                    new_acc + n.data_set_acc - AccValue::from_set(&sets_inter, pk);
                                let node_data_set = n.data_set.clone();
                                let node_acc = n.data_set_acc;
                                let (node_leaf_id, node_leaf_hash) = self.write_leaf(
                                    SmolStr::from(&rest_node_key),
                                    node_data_set,
                                    node_acc,
                                );

                                let mut btree_map: BTreeMap<char, (TrieNodeId, Digest)> =
                                    BTreeMap::new();
                                btree_map.insert(node_idx, (node_leaf_id, node_leaf_hash));
                                let non_leaf = TrieNonLeafNode::new(
                                    SmolStr::from(&common_key),
                                    non_leaf_set,
                                    non_leaf_acc,
                                    btree_map,
                                );
                                temp_nodes.push(TempNode::NonLeaf {
                                    node: non_leaf,
                                    idx: cur_idx,
                                });

                                let (leaf_id, leaf_hash) =
                                    self.write_leaf(SmolStr::from(&rest_cur_key), set, new_acc);
                                temp_nodes.push(TempNode::Leaf {
                                    id: leaf_id,
                                    hash: leaf_hash,
                                });
                            }
                            break;
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
                                                SmolStr::from(&common_key),
                                                non_leaf_set,
                                                non_leaf_acc,
                                                n.children.clone(),
                                            ),
                                            idx: cur_idx,
                                        });
                                        cur_id_opt = Some(*id);
                                        cur_key = SmolStr::from(&rest_cur_key);
                                    }
                                    None => {
                                        // no path, create leaf
                                        let non_leaf = TrieNonLeafNode::new(
                                            SmolStr::from(&common_key),
                                            non_leaf_set,
                                            non_leaf_acc,
                                            n.children.clone(),
                                        );
                                        let (new_leaf_id, new_leaf_hash) = self.write_leaf(
                                            SmolStr::from(&rest_cur_key),
                                            set,
                                            new_acc,
                                        );
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
                                let mut btree_map: BTreeMap<char, (TrieNodeId, Digest)> =
                                    BTreeMap::new();

                                let child_non_leaf = TrieNonLeafNode::new(
                                    SmolStr::from(&rest_node_key),
                                    n.data_set.clone(),
                                    n.data_set_acc,
                                    n.children.clone(),
                                );
                                let (child_non_leaf_id, child_non_leaf_hash) =
                                    self.write_non_leaf(child_non_leaf);
                                btree_map
                                    .insert(node_idx, (child_non_leaf_id, child_non_leaf_hash));

                                let (new_leaf_id, new_leaf_hash) =
                                    self.write_leaf(SmolStr::from(&rest_cur_key), set, new_acc);
                                let non_leaf = TrieNonLeafNode::new(
                                    SmolStr::from(&common_key),
                                    non_leaf_set,
                                    non_leaf_acc,
                                    btree_map,
                                );
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
                None => {
                    let (leaf_id, leaf_hash) = self.write_leaf(cur_key, set, new_acc);
                    temp_nodes.push(TempNode::Leaf {
                        id: leaf_id,
                        hash: leaf_hash,
                    });
                    break;
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
        self.apply.root.trie_root_id = Some(new_root_id);
        self.apply.root.trie_root_hash = new_root_hash;
        for id in self.outdated.drain() {
            self.apply.nodes.remove(&id);
        }

        Ok(())
    }

    pub fn delete(&mut self, key: SmolStr, obj_id: ObjId, pk: &AccPublicKey) -> Result<()> {
        let set = Set::from_single_element(obj_id.0);
        let delta_acc = AccValue::from_set(&set, pk);
        let mut cur_id_opt = self.apply.root.trie_root_id;
        let mut cur_key = key;

        #[allow(clippy::large_enum_variant)]
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
            match cur_id_opt {
                Some(id) => {
                    self.outdated.insert(id);
                    let cur_node = self.get_node(id)?;
                    match cur_node.as_ref() {
                        TrieNode::Leaf(n) => {
                            if cur_key == n.rest {
                                let set_dif = (&n.data_set) / (&set);
                                let old_acc = n.data_set_acc;
                                let mut is_empty = false;
                                if set_dif.is_empty() {
                                    is_empty = true;
                                }
                                let (id, hash) =
                                    self.write_leaf(cur_key, set_dif, old_acc - delta_acc);
                                if is_empty {
                                    self.outdated.insert(id);
                                }
                                temp_nodes.push(TempNode::Leaf { id, hash, is_empty });
                                break;
                            } else {
                                return Err(anyhow!("Key {} not found for trie", cur_key));
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
                                    cur_id_opt = Some(*id);
                                    cur_key = SmolStr::from(&rest_cur_key);
                                }
                                None => {
                                    return Err(anyhow!("Cannot find trie non-leaf node"));
                                }
                            }
                        }
                    }
                }
                None => {
                    bail!("Trie root id is None");
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
                        let mut new_str: SmolStr = node.nibble;
                        for (c, (id, _hash)) in node.children {
                            self.outdated.insert(id);
                            let child_n = self.get_node(id)?;
                            match child_n.as_ref() {
                                TrieNode::Leaf(n) => {
                                    if c == '\0' {
                                        let mut a = new_str.to_string();
                                        let b = n.rest.as_str();
                                        a.push_str(b);
                                        new_str = SmolStr::from(&a);
                                    } else {
                                        let mut a: String = new_str.to_string();
                                        let b = n.rest.as_str();
                                        a.push(c);
                                        a.push_str(b);
                                        new_str = SmolStr::from(&a);
                                    }
                                    let new_set = n.data_set.clone();
                                    let new_acc = n.data_set_acc;
                                    let (new_id, new_hash) =
                                        self.write_leaf(new_str.clone(), new_set, new_acc);
                                    new_root_id = new_id;
                                    new_root_hash = new_hash;
                                }
                                TrieNode::NonLeaf(n) => {
                                    let mut a: String = new_str.to_string();
                                    let b = n.nibble.as_str();
                                    if c != '\0' {
                                        a.push(c);
                                    }
                                    a.push_str(b);
                                    new_str = SmolStr::from(&a);
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

        self.apply.root.trie_root_id = Some(new_root_id);
        self.apply.root.trie_root_hash = new_root_hash;

        for id in self.outdated.drain() {
            self.apply.nodes.remove(&id);
        }

        Ok(())
    }
}
