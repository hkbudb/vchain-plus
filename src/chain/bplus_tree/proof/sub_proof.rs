use crate::{
    acc::{set::Set, AccPublicKey, AccValue},
    chain::{
        bplus_tree::proof::{
            leaf::BPlusTreeLeaf, non_leaf::BPlusTreeNonLeaf, res_sub_tree::BPlusTreeResSubTree,
            sub_tree::BPlusTreeSubTree,
        },
        range::Range,
        traits::Num,
    },
    digest::{Digest, Digestible},
};
use anyhow::{anyhow, ensure, Result};
use serde::{Deserialize, Serialize};
use std::collections::VecDeque;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) enum SubProof<K: Num> {
    Hash(Box<BPlusTreeSubTree<K>>),
    Leaf(Box<BPlusTreeLeaf<K>>),
    NonLeaf(Box<BPlusTreeNonLeaf<K>>),
    ResSubTree(Box<BPlusTreeResSubTree<K>>),
}

impl<K: Num> Digestible for SubProof<K> {
    fn to_digest(&self) -> Digest {
        match self {
            Self::Hash(n) => n.to_digest(),
            Self::Leaf(n) => n.to_digest(),
            Self::NonLeaf(n) => n.to_digest(),
            Self::ResSubTree(n) => n.to_digest(),
        }
    }
}

impl<K: Num> SubProof<K> {
    pub(crate) fn from_hash(range: Range<K>, node_hash: Digest) -> Self {
        Self::Hash(Box::new(BPlusTreeSubTree::new(range, node_hash)))
    }

    pub(crate) fn from_leaf(l: BPlusTreeLeaf<K>) -> Self {
        Self::Leaf(Box::new(l))
    }

    pub(crate) fn from_non_leaf(n: BPlusTreeNonLeaf<K>) -> Self {
        Self::NonLeaf(Box::new(n))
    }

    pub(crate) fn from_res_sub_tree(n: BPlusTreeResSubTree<K>) -> Self {
        Self::ResSubTree(Box::new(n))
    }

    pub(crate) fn value_acc_completeness(
        &self,
        range: Range<K>,
        pk: &AccPublicKey,
    ) -> Result<AccValue> {
        let mut res_acc_val: AccValue = AccValue::from_set(&Set::new(), pk);
        let mut completeness = true;
        let cur_proof = Box::new(self.clone());
        let mut queue: VecDeque<Box<SubProof<K>>> = VecDeque::new();
        queue.push_back(cur_proof);

        while let Some(cur_proof) = queue.pop_front() {
            match *cur_proof {
                SubProof::Hash(n) => {
                    if !n.range.has_no_intersection(range) {
                        completeness = false;
                    }
                }
                SubProof::Leaf(n) => {
                    if !range.is_in_range(n.num) {
                        completeness = false;
                    }
                    res_acc_val = res_acc_val + n.acc_val;
                }
                SubProof::NonLeaf(n) => {
                    for child in n.children {
                        queue.push_back(child.ok_or_else(|| anyhow!("Subproof is None"))?);
                    }
                }
                SubProof::ResSubTree(n) => {
                    if !n.range.is_covered(range) {
                        completeness = false;
                    }
                    res_acc_val = res_acc_val + n.acc_val;
                }
            }
        }

        ensure!(completeness, "Completeness not satisfied");

        Ok(res_acc_val)
    }
}
