use super::hash::merkle_proof_hash;
use crate::{
    acc::{AccValue, FinalProof, IntermediateProof, Set},
    chain::{
        block::Height,
        bplus_tree,
        id_tree::{self, ObjId},
        range::Range,
        traits::Num,
        trie_tree,
    },
    digest::Digest,
};
use anyhow::{bail, Result};
use petgraph::{graph::NodeIndex, Graph};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap};

#[derive(Debug)]
pub enum VONode<K: Num> {
    Range(VORangeNode<K>),
    Keyword(VOKeywordNode),
    BlkRt(VOBlkRtNode),
    InterUnion(VOInterUnion),
    FinalUnion(VOFinalUnion),
    InterIntersec(VOInterIntersec),
    FinalIntersec(VOFinalIntersec),
    InterDiff(VOInterDiff),
    FinalDiff(VOFinalDiff),
}

impl<K: Num> VONode<K> {
    pub(crate) fn get_acc(&self) -> Result<&AccValue> {
        match self {
            VONode::Range(n) => Ok(&n.acc),
            VONode::Keyword(n) => Ok(&n.acc),
            VONode::BlkRt(n) => Ok(&n.acc),
            VONode::InterUnion(n) => Ok(&n.acc),
            VONode::FinalUnion(_) => bail!("This is a final operation"),
            VONode::InterIntersec(n) => Ok(&n.acc),
            VONode::FinalIntersec(_) => bail!("This is a final operation"),
            VONode::InterDiff(n) => Ok(&n.acc),
            VONode::FinalDiff(_) => bail!("This is a final operation"),
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VORangeNode<K: Num> {
    pub(crate) range: Range<K>,
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
    pub(crate) dim: usize,
    pub(crate) acc: AccValue,
    pub(crate) proof: bplus_tree::proof::Proof<K>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VOKeywordNode {
    pub(crate) keyword: String,
    pub(crate) blk_height: Height,
    pub(crate) time_win: u64,
    pub(crate) acc: AccValue,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VOBlkRtNode {
    pub(crate) blk_height: Height,
    pub(crate) acc: AccValue,
}

#[derive(Debug)]
pub struct VOInterUnion {
    pub(crate) acc: AccValue,
    pub(crate) proof: IntermediateProof,
}

#[derive(Debug)]
pub struct VOFinalUnion {
    pub(crate) proof: FinalProof,
}

#[derive(Debug)]
pub struct VOInterIntersec {
    pub(crate) acc: AccValue,
    pub(crate) proof: IntermediateProof,
}

#[derive(Debug)]
pub struct VOFinalIntersec {
    pub(crate) proof: FinalProof,
}

#[derive(Debug)]
pub struct VOInterDiff {
    pub(crate) acc: AccValue,
    pub(crate) proof: IntermediateProof,
}

#[derive(Debug)]
pub struct VOFinalDiff {
    pub(crate) proof: FinalProof,
}

pub struct MerkleProof {
    pub(crate) id_tree_root_hash: Option<Digest>,
    pub(crate) id_set_root_hash: Digest,
    pub(crate) ads_hashes: BTreeMap<u64, Digest>,
}

impl MerkleProof {
    pub(crate) fn ads_root_hash(&self, id_tree_root_hash: &Digest) -> Digest {
        merkle_proof_hash(
            &self.id_set_root_hash,
            id_tree_root_hash,
            self.ads_hashes.iter(),
        )
    }

    pub(crate) fn insert_ads_hash(&mut self, time_win: u64, ads_hash: Digest) {
        self.ads_hashes.insert(time_win, ads_hash);
    }
}

pub struct VoDag<K: Num> {
    pub(crate) output_sets: HashMap<NodeIndex, Set>,
    pub(crate) dag: Graph<VONode<K>, ()>,
}

pub struct VO<K: Num> {
    pub(crate) vo_dag: VoDag<K>,
    pub(crate) trie_proofs: HashMap<Height, trie_tree::proof::Proof>,
    pub(crate) id_tree_proof: id_tree::proof::Proof,
    pub(crate) cur_obj_id: ObjId,
    pub(crate) merkle_proofs: HashMap<Height, MerkleProof>,
}
