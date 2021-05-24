use super::{
    proof::{sub_proof::SubProof, Proof},
    write::fanout_nary_rev,
    Digest, IdTreeNode, IdTreeNodeId, IdTreeNodeLoader, IdTreeObjId,
};
use crate::{digest::Digestible};
use anyhow::{anyhow, bail, Result};

pub fn query_without_proof(
    n_k: usize,
    node_loader: impl IdTreeNodeLoader,
    root_id: IdTreeNodeId,
    obj_id: IdTreeObjId,
    fanout: usize,
) -> Result<Option<Digest>> {
    let root_node = match node_loader.load_node(root_id)? {
        Some(n) => n,
        None => return Ok(None),
    };

    let mut cur_node = root_node;
    let depth = (n_k as f64).log(fanout as f64).floor() as usize;
    let mut cur_path_rev = fanout_nary_rev(obj_id.get_num(), fanout as u64, depth);

    let value = loop {
        match &cur_node {
            IdTreeNode::Leaf(n) => {
                if obj_id == n.obj_id {
                    break Some(n.obj_hash);
                } else {
                    break None;
                }
            }
            IdTreeNode::NonLeaf(n) => {
                let idx = cur_path_rev
                    .pop()
                    .ok_or_else(|| anyhow!("Current path is empty!"))?;
                let child_id = *n
                    .get_child_id(idx)
                    .ok_or_else(|| anyhow!("Cannot find child id!"))?;
                if let Some(child_node) = node_loader.load_node(child_id)? {
                    cur_node = child_node;
                    continue;
                }
            }
        }
    };

    Ok(value)
}

fn inner_query_id_tree(
    node_loader: &impl IdTreeNodeLoader,
    root_id: IdTreeNodeId,
    root_node: IdTreeNode,
    obj_id: IdTreeObjId,
    path_rev: &mut Vec<usize>,
) -> Result<(Option<Digest>, SubProof)> {
    use super::proof::{leaf::IdTreeLeaf, non_leaf::IdTreeNonLeaf};

    let mut query_proof = SubProof::from_hash(root_id, root_node.to_digest());
    let mut query_val: Option<Digest> = None;

    let mut cur_node = root_node;
    let cur_path_rev = path_rev;
    let mut cur_proof = &mut query_proof as *mut _;

    loop {
        match &cur_node {
            IdTreeNode::Leaf(n) => {
                query_val = if obj_id == n.obj_id {
                    Some(n.obj_hash)
                } else {
                    None
                };

                unsafe {
                    *cur_proof =
                        SubProof::from_leaf(IdTreeLeaf::new(n.obj_id, n.id, n.to_digest()));
                }
                break;
            }
            IdTreeNode::NonLeaf(n) => {
                if let Some(child_idx) = cur_path_rev.pop() {
                    if let (Some(child_id), Some(child_hash)) =
                        (n.get_child_id(child_idx), n.get_child_hash(child_idx))
                    {
                        if let Some(sub_node) = node_loader.load_node(*child_id)? {
                            let mut sub_proof =
                                Box::new(SubProof::from_hash(*child_id, *child_hash));
                            let sub_proof_ptr = &mut *sub_proof as *mut _;
                            let mut non_leaf =
                                IdTreeNonLeaf::from_hashes(n.child_hashes.clone(), n.child_ids.clone());
                            *non_leaf.get_child_mut(child_idx) = Some(sub_proof);
                            unsafe {
                                *cur_proof = SubProof::from_non_leaf(non_leaf);
                            }
                            cur_node = sub_node;
                            cur_proof = sub_proof_ptr;
                            continue;
                        }
                    }
                } else {
                    bail!("Invalid obj_id");
                }
                let non_leaf = IdTreeNonLeaf::from_hashes(n.child_hashes.clone(), n.child_ids.clone());

                unsafe {
                    *cur_proof = SubProof::from_non_leaf(non_leaf);
                }
                break;
            }
        }
    }

    Ok((query_val, query_proof))
}

pub fn query_id_tree(
    n_k: usize,
    node_loader: &impl IdTreeNodeLoader,
    root_id: IdTreeNodeId,
    obj_id: IdTreeObjId,
    fanout: usize,
) -> Result<(Option<Digest>, Proof)> {
    let root_node = match node_loader.load_node(root_id)? {
        Some(n) => n,
        None => return Ok((None, Proof::from_root_hash(root_id, Digest::zero()))),
    };
    let depth = (n_k as f64).log(fanout as f64).floor() as usize;
    let mut cur_path_rev = fanout_nary_rev(obj_id.get_num(), fanout as u64, depth);
    let (v, p) = inner_query_id_tree(node_loader, root_id, root_node, obj_id, &mut cur_path_rev)?;
    Ok((v, Proof::from_subproof(p)))
}

pub struct ReadContext<L: IdTreeNodeLoader> {
    node_loader: L,
    root_id: IdTreeNodeId,
    proof: Proof,
}

impl<L: IdTreeNodeLoader> ReadContext<L> {
    pub fn new(node_loader: L, root_id: IdTreeNodeId) -> Self {
        match node_loader.load_node(root_id) {
            Ok(n) => {
                let dig = n.unwrap().to_digest();
                Self {
                    node_loader,
                    root_id,
                    proof: Proof::from_root_hash(root_id, dig),
                }
            }
            Err(_) => Self {
                node_loader,
                root_id,
                proof: Proof::from_root_hash(root_id, Digest::zero()),
            },
        }
    }

    pub fn get_node_loader(&self) -> &L {
        &self.node_loader
    }

    pub fn get_node_loader_mut(&mut self) -> &mut L {
        &mut self.node_loader
    }

    pub fn get_proof(&self) -> &Proof {
        &self.proof
    }

    pub fn into_proof(self) -> Proof {
        self.proof
    }

    pub fn query(&mut self, n_k: usize, obj_id: IdTreeObjId, fanout: usize) -> Result<Option<Digest>> {
        let value = match self.proof.root.as_mut() {
            Some(root) => {
                let depth = (n_k as f64).log(fanout as f64).floor() as usize;
                let mut cur_path_rev =
                    fanout_nary_rev(obj_id.get_num(), fanout as u64, depth);

                match root.search_prefix(obj_id, &mut cur_path_rev) {
                    Some((sub_proof, sub_root_id, sub_path)) => {
                        let sub_root_node = self
                            .node_loader
                            .load_node(sub_root_id)?
                            .ok_or_else(|| anyhow!("Cannot find sub-root node!"))?;
                        let (v, p) = inner_query_id_tree(
                            &self.node_loader,
                            sub_root_id,
                            sub_root_node,
                            obj_id,
                            sub_path,
                        )?;
                        unsafe {
                            *sub_proof = p;
                        }
                        v
                    }
                    None => None,
                }
            }
            None => {
                let (v, p) = query_id_tree(n_k, &self.node_loader, self.root_id, obj_id, fanout)?;
                self.proof = p;
                v
            }
        };
        Ok(value)
    }
}
