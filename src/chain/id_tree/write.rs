use super::{
    Digest, Digestible, IdTreeLeafNode, IdTreeNode, IdTreeNodeId, IdTreeNodeLoader,
    IdTreeNonLeafNode, IdTreeObjId,
};
use anyhow::{anyhow, Result};
use serde::{Deserialize, Serialize};
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Apply {
    pub root_id: IdTreeNodeId,
    pub nodes: HashMap<IdTreeNodeId, IdTreeNode>,
}

pub struct WriteContext<L: IdTreeNodeLoader> {
    node_loader: L,
    apply: Apply,
    outdated: HashSet<IdTreeNodeId>,
}

impl<L: IdTreeNodeLoader> WriteContext<L> {
    pub fn new(node_loader: L, root_id: IdTreeNodeId) -> Self {
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

    pub fn write_leaf(&mut self, obj_id: IdTreeObjId, obj_hash: Digest) -> (IdTreeNodeId, Digest) {
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

    fn get_node(&self, id: IdTreeNodeId) -> Result<Option<Cow<IdTreeNode>>> {
        Ok(match self.apply.nodes.get(&id) {
            Some(n) => Some(Cow::Borrowed(n)),
            None => self.node_loader.load_node(id)?.map(Cow::Owned),
        })
    }

    pub fn insert(
        &mut self,
        obj_id: IdTreeObjId,
        obj_hash: Digest,
        n_k: usize,
        fanout: usize,
    ) -> Result<()> {
        let mut cur_id = self.apply.root_id;
        let depth = (n_k as f64).log(fanout as f64).floor() as usize;
        let mut cur_path_rev = fanout_nary_rev(obj_id.get_num(), fanout as u64, depth);

        enum TempNode {
            Leaf { id: IdTreeNodeId, hash: Digest },
            NonLeaf { node: IdTreeNonLeafNode, idx: usize },
        }

        let mut temp_nodes: Vec<TempNode> = Vec::new();

        loop {
            self.outdated.insert(cur_id);
            let cur_node = match self.get_node(cur_id)? {
                Some(n) => n,
                None => {
                    loop {
                        if cur_path_rev.is_empty() {
                            let (leaf_id, leaf_hash) = self.write_leaf(obj_id, obj_hash);
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
            };

            match cur_node.as_ref() {
                IdTreeNode::Leaf(_n) => {
                    let (leaf_id, leaf_hash) = self.write_leaf(obj_id, obj_hash);
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
                        node: IdTreeNonLeafNode::new(n.child_hashes.clone(), n.child_ids.clone()),
                        idx,
                    });

                    cur_id = *n
                        .get_child_id(idx)
                        .ok_or_else(|| anyhow!("Cannot find child id!"))?;
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
        self.apply.root_id = new_root_id;

        for id in self.outdated.drain() {
            self.apply.nodes.remove(&id);
        }

        Ok(())
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
        //dbg!(v_ten);

        let expect_two: Vec<usize> = vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
        let v_two: Vec<usize> = fanout_nary_rev(1025, 2, 11);
        assert_eq!(v_two, expect_two);

        let expect_two_2: Vec<usize> = vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0];
        let v_two_2: Vec<usize> = fanout_nary_rev(1025, 2, 12);
        assert_eq!(v_two_2, expect_two_2);
    }
}
