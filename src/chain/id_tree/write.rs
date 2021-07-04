use crate::chain::id_tree::{
    Digest, Digestible, IdTreeInternalId, IdTreeLeafNode, IdTreeNode, IdTreeNodeId,
    IdTreeNodeLoader, IdTreeNonLeafNode, IdTreeRoot, ObjId,
};
use anyhow::{anyhow, Result};
use serde::{Deserialize, Serialize};
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Apply {
    pub root: IdTreeRoot,
    pub nodes: HashMap<IdTreeNodeId, IdTreeNode>,
}

pub struct WriteContext<'a, L: IdTreeNodeLoader> {
    node_loader: &'a L,
    apply: Apply,
    outdated: HashSet<IdTreeNodeId>,
}

impl<'a, L: IdTreeNodeLoader> WriteContext<'a, L> {
    pub fn new(node_loader: &'a L, root: IdTreeRoot) -> Self {
        IdTreeNodeId::next_id();
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
        obj_id: IdTreeInternalId,
        obj_hash: Digest,
    ) -> (IdTreeNodeId, Digest) {
        let node = IdTreeLeafNode::new(obj_id, obj_hash);
        let id = node.id;
        let hash = node.to_digest();
        self.apply.nodes.insert(id, IdTreeNode::from_leaf(node));
        (id, hash)
    }

    pub fn write_non_leaf(&mut self, n: IdTreeNonLeafNode) -> (IdTreeNodeId, Digest) {
        let id = n.id;
        let hash = n.to_digest();
        self.apply.nodes.insert(id, IdTreeNode::from_non_leaf(n));
        (id, hash)
    }

    fn get_node(&self, id: IdTreeNodeId) -> Result<Cow<IdTreeNode>> {
        Ok(match self.apply.nodes.get(&id) {
            Some(n) => Cow::Borrowed(n),
            None => Cow::Owned(self.node_loader.load_node(id)?),
        })
    }

    pub fn insert(&mut self, obj_hash: Digest, max_id_num: usize, fanout: usize) -> Result<ObjId> {
        let cur_id = self.apply.root.cur_obj_id;
        let internal_id = cur_id.to_internal_id();
        let next_internal_id = IdTreeInternalId((internal_id.0 + 1) % max_id_num as u64);
        self.apply.root.cur_obj_id = ObjId::from_internal_id(next_internal_id);
        let mut cur_id_opt = self.apply.root.id_tree_root_id;
        let depth = (max_id_num as f64).log(fanout as f64).floor() as usize;
        let mut cur_path_rev = fanout_nary_rev(internal_id.0, fanout as u64, depth);

        #[allow(clippy::large_enum_variant)]
        enum TempNode {
            Leaf { id: IdTreeNodeId, hash: Digest },
            NonLeaf { node: IdTreeNonLeafNode, idx: usize },
        }

        let mut temp_nodes: Vec<TempNode> = Vec::new();
        loop {
            match cur_id_opt {
                Some(id) => {
                    self.outdated.insert(id);
                    let cur_node = self.get_node(id)?;
                    match cur_node.as_ref() {
                        IdTreeNode::Leaf(_n) => {
                            let (leaf_id, leaf_hash) = self.write_leaf(internal_id, obj_hash);
                            temp_nodes.push(TempNode::Leaf {
                                id: leaf_id,
                                hash: leaf_hash,
                            });
                            break;
                        }
                        IdTreeNode::NonLeaf(n) => {
                            let idx = cur_path_rev
                                .pop()
                                .ok_or_else(|| anyhow!("Path is empty!"))?;
                            temp_nodes.push(TempNode::NonLeaf {
                                node: IdTreeNonLeafNode::new(
                                    n.child_hashes.clone(),
                                    n.child_ids.clone(),
                                ),
                                idx,
                            });

                            let cur_id = *n
                                .get_child_id(idx)
                                .ok_or_else(|| anyhow!("Cannot find child id!"))?;
                            if cur_id == IdTreeNodeId(0) {
                                cur_id_opt = None;
                            } else {
                                cur_id_opt = Some(cur_id);
                            }
                        }
                    }
                }
                None => {
                    loop {
                        if cur_path_rev.is_empty() {
                            let (leaf_id, leaf_hash) = self.write_leaf(internal_id, obj_hash);
                            temp_nodes.push(TempNode::Leaf {
                                id: leaf_id,
                                hash: leaf_hash,
                            });
                            break;
                        } else {
                            let idx = cur_path_rev
                                .pop()
                                .ok_or_else(|| anyhow!("Path is empty!"))?;
                            let non_leaf = IdTreeNonLeafNode::new_ept();
                            temp_nodes.push(TempNode::NonLeaf {
                                node: non_leaf,
                                idx,
                            });
                        }
                    }
                    break;
                }
            }
        }

        let mut new_root_id = IdTreeNodeId::next_id();
        let mut new_root_hash = Digest::zero();
        for node in temp_nodes.into_iter().rev() {
            match node {
                TempNode::Leaf { id, hash } => {
                    new_root_id = id;
                    new_root_hash = hash;
                }
                TempNode::NonLeaf { mut node, idx } => {
                    *node
                        .get_child_id_mut(idx)
                        .ok_or_else(|| anyhow!("Cannot find child id!"))? = new_root_id;
                    *node
                        .get_child_hash_mut(idx)
                        .ok_or_else(|| anyhow!("Cannot find child hash!"))? = new_root_hash;
                    let (id, hash) = self.write_non_leaf(node);
                    new_root_id = id;
                    new_root_hash = hash;
                }
            }
        }
        self.apply.root.id_tree_root_id = Some(new_root_id);
        self.apply.root.id_tree_root_hash = new_root_hash;

        for id in self.outdated.drain() {
            self.apply.nodes.remove(&id);
        }

        Ok(cur_id)
    }
}

pub fn fanout_nary_rev(obj_id: u64, fanout: u64, depth: usize) -> Vec<usize> {
    let mut path: Vec<usize> = vec![0; depth];
    let mut num = obj_id;
    let mut idx_size = 0;
    while idx_size < depth {
        path[idx_size] = (num % fanout) as usize;
        num /= fanout;
        idx_size += 1;
    }
    path
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_fanout_nary() {
        use super::fanout_nary_rev;

        let expect_ten: Vec<usize> = vec![1, 3, 0, 7, 9, 1];
        let v_ten: Vec<usize> = fanout_nary_rev(197031, 10, 6);
        assert_eq!(v_ten, expect_ten);

        let expect_two: Vec<usize> = vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
        let v_two: Vec<usize> = fanout_nary_rev(1025, 2, 11);
        assert_eq!(v_two, expect_two);

        let expect_two_2: Vec<usize> = vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0];
        let v_two_2: Vec<usize> = fanout_nary_rev(1025, 2, 12);
        assert_eq!(v_two_2, expect_two_2);
    }
}
