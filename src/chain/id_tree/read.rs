use super::{
    Digest, IdTreeNode, IdTreeNodeId, IdTreeNodeLoader,
    IdTreeNonLeafNode, IdTreeObjId, write::fanout_nary_rev,
};
use crate::chain::{object::ObjId, MAX_FANOUT};
use anyhow::Result;

pub fn query_without_proof(
    n_k: usize,
    node_loader: impl IdTreeNodeLoader,
    root_id: IdTreeNodeId,
    raw_obj_id: ObjId,
) -> Result<Option<Digest>> {
    let root_node = match node_loader.load_node(root_id)? {
        Some(n) => n,
        None => return Ok(None),
    };

    let mut cur_node = root_node;

    let obj_id = IdTreeObjId(raw_obj_id.unwrap() % n_k as u64);
    let depth = (n_k as f64).log(MAX_FANOUT as f64).floor() as usize;
    let mut cur_path_rev = fanout_nary_rev(obj_id.unwrap(), MAX_FANOUT as u64, depth);

    let value = loop {
        match &cur_node {
            IdTreeNode::Leaf(n) => {
                if obj_id == n.obj_id {
                    break Some(n.obj_hash);
                } else {
                    break None;
                }
            },
            IdTreeNode::NonLeaf(n) => {
                let idx = cur_path_rev.pop().unwrap();
                let child_id = *n.get_child_id(idx).unwrap();
                if let Some(child_node) = node_loader.load_node(child_id)? {
                    cur_node = child_node;
                    continue;
                }
            }
        }
    };

    Ok(value)
}
