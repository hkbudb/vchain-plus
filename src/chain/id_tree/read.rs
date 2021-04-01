use super::{
    Digest, Digestible, IdTreeLeafNode, IdTreeNode, IdTreeNodeId, IdTreeNodeLoader,
    IdTreeNonLeafNode, IdTreeObjId,
};
use crate::chain::{object::ObjId, MAX_FANOUT};
use anyhow::Result;

pub fn query_without_proof(
    node_loader: &impl IdTreeNodeLoader,
    raw_obj_id:ObjId,
) -> Result<Option<Digest>> {
    todo!()
}
