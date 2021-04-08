use super::sub_proof::SubProof;
use crate::{chain::id_tree::{hash::id_tree_non_leaf_proof_hash, IdTreeObjId, IDTREE_FANOUT}, create_id_type, digest::{Digest, Digestible}};
use serde::{Deserialize, Serialize};
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub(crate) struct IdTreeNonLeaf {
    pub(crate) children: [Option<Box<SubProof>>; IDTREE_FANOUT],
}

impl Digestible for IdTreeNonLeaf {
    fn to_digest(&self) -> Digest {
        let children = self
            .children
            .iter()
            .map(|c| c.as_ref().map(|n| n.to_digest()));
        id_tree_non_leaf_proof_hash(children)
    }
}

impl IdTreeNonLeaf {
    pub(crate) fn from_hashes(children: &[Digest; IDTREE_FANOUT]) -> Self {
        let mut node = IdTreeNonLeaf::default();
        for (i, child) in children.iter().enumerate() {
            node.children[i] = Some(Box::new(SubProof::Hash(*child)));
        }
        node
    }

    pub(crate) fn get_child(&self, index: usize) -> Option<&'_ SubProof> {
        unsafe { self.children.get_unchecked(index) }
            .as_ref()
            .map(|n| n.as_ref())
    }

    pub(crate) fn get_child_mut(&mut self, index: usize) -> &'_ mut Option<Box<SubProof>> {
        unsafe { self.children.get_unchecked_mut(index) }
    }

    pub(crate) fn set_child(&mut self, index: usize, child: SubProof) {
        self.children[index] = Some(Box::new(child));
    }

    pub(crate) fn value_hash(
        &self,
        obj_id: IdTreeObjId,
        cur_path_rev: &mut Vec<usize>,
    ) -> Option<Digest> {
        let child_idx = cur_path_rev.pop().unwrap();
        match self.get_child(child_idx) {
            None => Some(Digest::zero()),
            Some(child) => child.value_hash(obj_id, cur_path_rev),
        }
    }

    pub(crate) fn search_prefix<'a>(
        &mut self,
        obj_id: IdTreeObjId,
        cur_path_rev: &'a mut Vec<usize>,
    ) -> Option<(*mut SubProof, Digest, &'a mut Vec<usize>)> {
        let child_idx = cur_path_rev.pop().unwrap();
        match self.get_child_mut(child_idx) {
            Some(child) => child.search_prefix(obj_id, cur_path_rev),
            None => None,
        }
    }
}
