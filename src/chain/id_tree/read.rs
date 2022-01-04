use crate::{
    chain::id_tree::{
        proof::{sub_proof::SubProof, Proof},
        write::fanout_nary_rev,
        Digest, IdTreeInternalId, IdTreeNode, IdTreeNodeId, IdTreeNodeLoader, ObjId,
    },
    digest::Digestible,
};
use anyhow::{anyhow, bail, Context, Result};

pub fn query_without_proof(
    max_id_num: u16,
    node_loader: impl IdTreeNodeLoader,
    root_id: IdTreeNodeId,
    obj_id: IdTreeInternalId,
    fanout: u8,
) -> Result<Option<Digest>> {
    let root_node = node_loader.load_node(root_id)?;

    let mut cur_node = root_node;
    let depth = (max_id_num as f64).log(fanout as f64).floor() as usize;
    let mut cur_path_rev = fanout_nary_rev(obj_id.0, fanout, depth);

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
                cur_node = node_loader.load_node(child_id)?;
            }
        }
    };

    Ok(value)
}

fn inner_query_id_tree(
    node_loader: &impl IdTreeNodeLoader,
    root_id: IdTreeNodeId,
    root_node: IdTreeNode,
    obj_id: IdTreeInternalId,
    path_rev: &mut Vec<usize>,
) -> Result<(Option<Digest>, SubProof)> {
    use super::proof::{leaf::IdTreeLeaf, non_leaf::IdTreeNonLeaf};

    let mut query_proof = SubProof::from_hash(Some(root_id), root_node.to_digest());
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
                        SubProof::from_leaf(IdTreeLeaf::new(n.obj_id, Some(n.id), n.to_digest()));
                }
                break;
            }
            IdTreeNode::NonLeaf(n) => {
                let child_idx = cur_path_rev.pop().context("Invalid obj_id")?;
                if let (Some(child_id), Some(child_hash)) =
                    (n.get_child_id(child_idx), n.get_child_hash(child_idx))
                {
                    let sub_node = node_loader.load_node(*child_id)?;
                    let mut sub_proof = Box::new(SubProof::from_hash(Some(*child_id), *child_hash));
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
                let non_leaf =
                    IdTreeNonLeaf::from_hashes(n.child_hashes.clone(), n.child_ids.clone());

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
    max_id_num: u16,
    node_loader: &impl IdTreeNodeLoader,
    root_id: Option<IdTreeNodeId>,
    obj_id: IdTreeInternalId,
    fanout: u8,
) -> Result<(Option<Digest>, Proof)> {
    let id_tree_root_id = match root_id {
        Some(id) => id,
        None => bail!("The id tree is empty"),
    };
    let root_node = node_loader.load_node(id_tree_root_id)?;
    let depth = (max_id_num as f64).log(fanout as f64).floor() as usize;
    let mut cur_path_rev = fanout_nary_rev(obj_id.0, fanout, depth);
    let (v, p) = inner_query_id_tree(
        node_loader,
        id_tree_root_id,
        root_node,
        obj_id,
        &mut cur_path_rev,
    )?;
    Ok((v, Proof::from_subproof(p)))
}

pub struct ReadContext<'a, L: IdTreeNodeLoader> {
    node_loader: &'a L,
    root_id: Option<IdTreeNodeId>,
    proof: Proof,
}

impl<'a, L: IdTreeNodeLoader> ReadContext<'a, L> {
    pub fn new(node_loader: &'a L, root_id: Option<IdTreeNodeId>) -> Self {
        match root_id {
            Some(id) => match node_loader.load_node(id) {
                Ok(n) => {
                    let dig = n.to_digest();
                    Self {
                        node_loader,
                        root_id,
                        proof: Proof::from_root_hash(Some(id), dig),
                    }
                }
                Err(_) => Self {
                    node_loader,
                    root_id,
                    proof: Proof::from_root_hash(Some(id), Digest::zero()),
                },
            },
            None => Self {
                node_loader,
                root_id,
                proof: Proof::from_root_hash(None, Digest::zero()),
            },
        }
    }

    pub fn get_node_loader(&self) -> &L {
        self.node_loader
    }

    pub fn get_proof(&self) -> &Proof {
        &self.proof
    }

    pub fn into_proof(self) -> Proof {
        let mut proof = self.proof;
        proof.remove_node_id();
        proof
    }

    pub fn query(&mut self, obj_id: ObjId, max_id_num: u16, fanout: u8) -> Result<Option<Digest>> {
        let internal_id: IdTreeInternalId = obj_id.to_internal_id();
        let value = match self.proof.root.as_mut() {
            Some(root) => {
                let depth = (max_id_num as f64).log(fanout as f64).floor() as usize;
                let mut cur_path_rev = fanout_nary_rev(internal_id.0, fanout, depth);

                match root.search_prefix(internal_id, &mut cur_path_rev) {
                    Some((sub_proof, sub_root_id_opt, sub_path)) => {
                        let sub_root_id = sub_root_id_opt.context("Sub root id is none")?;
                        let sub_root_node = self.node_loader.load_node(sub_root_id)?;
                        let (v, p) = inner_query_id_tree(
                            self.node_loader,
                            sub_root_id,
                            sub_root_node,
                            internal_id,
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
                let (v, p) = query_id_tree(
                    max_id_num,
                    self.node_loader,
                    self.root_id,
                    internal_id,
                    fanout,
                )?;
                self.proof = p;
                v
            }
        };
        Ok(value)
    }
}
