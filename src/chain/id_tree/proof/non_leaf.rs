use super::sub_proof::SubProof;
use crate::{
    chain::id_tree::{hash::id_tree_non_leaf_proof_hash, MAX_FANOUT},
    digest::{Digest, Digestible},
};
use serde::{Deserialize, Serialize};
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub(crate) struct IdTreeNonLeaf {
    pub(crate) children: [Option<Box<SubProof>>; MAX_FANOUT],
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
    pub(crate) fn from_hashes(children: &[Option<Digest>; MAX_FANOUT]) -> Self {
        let mut node = IdTreeNonLeaf::default();
        for (i, child) in children.iter().enumerate() {
            if let Some(hash) = child {
                unsafe {
                    *node.children.get_unchecked_mut(i) = Some(Box::new(SubProof::Hash(*hash)));
                }
            }
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
}
