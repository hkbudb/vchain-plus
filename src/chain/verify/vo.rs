use crate::{
    acc::{AccValue, FinalProof, IntermediateProof, Set},
    chain::{
        block::Height,
        bplus_tree,
        id_tree::{self, ObjId},
        traits::Num,
        trie_tree,
        verify::hash::merkle_proof_hash,
    },
    digest::Digest,
};
use anyhow::{bail, Result};
use petgraph::graph::NodeIndex;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap};

#[derive(Debug, Serialize, Deserialize)]
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
            VONode::FinalUnion(_) => bail!("This is a final union operation"),
            VONode::InterIntersec(n) => Ok(&n.acc),
            VONode::FinalIntersec(_) => bail!("This is a final intersec operation"),
            VONode::InterDiff(n) => Ok(&n.acc),
            VONode::FinalDiff(_) => bail!("This is a final diff operation"),
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VORangeNode<K: Num> {
    pub(crate) blk_height: Height,
    pub(crate) win_size: u16,
    pub(crate) acc: AccValue,
    pub(crate) proof: bplus_tree::proof::Proof<K>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VOKeywordNode {
    pub(crate) blk_height: Height,
    pub(crate) win_size: u16,
    pub(crate) acc: AccValue,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VOBlkRtNode {
    pub(crate) blk_height: Height,
    pub(crate) win_size: u16,
    pub(crate) acc: AccValue,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VOInterUnion {
    pub(crate) acc: AccValue,
    pub(crate) proof: IntermediateProof,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VOFinalUnion {
    pub(crate) proof: FinalProof,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VOInterIntersec {
    pub(crate) acc: AccValue,
    pub(crate) proof: Option<IntermediateProof>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VOFinalIntersec {
    pub(crate) proof: FinalProof,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VOInterDiff {
    pub(crate) acc: AccValue,
    pub(crate) proof: Option<IntermediateProof>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VOFinalDiff {
    pub(crate) proof: FinalProof,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct MerkleProof {
    pub(crate) id_tree_root_hash: Option<Digest>,
    pub(crate) id_set_root_hash: Digest,
    pub(crate) ads_hashes: BTreeMap<u16, Digest>,
    pub(crate) extra_bplus_rt_hashes: HashMap<u8, Digest>,
}

impl MerkleProof {
    pub(crate) fn ads_root_hash(
        &self,
        id_tree_root_hash: &Digest,
        rest_ads_hashes: impl Iterator<Item = (u16, Digest)>,
    ) -> Digest {
        let mut ads_hashes = self.ads_hashes.clone();
        for (time_win, hash) in rest_ads_hashes {
            ads_hashes.insert(time_win, hash);
        }
        merkle_proof_hash(&self.id_set_root_hash, id_tree_root_hash, ads_hashes.iter())
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VoDagContent<K: Num> {
    pub(crate) output_sets: HashMap<NodeIndex, Set>,
    pub(crate) dag_content: HashMap<NodeIndex, VONode<K>>,
}

#[derive(Serialize, Deserialize)]
pub struct VO<K: Num> {
    pub(crate) vo_dag_content: VoDagContent<K>,
    pub(crate) trie_proofs: HashMap<Height, trie_tree::proof::Proof>,
    pub(crate) id_tree_proof: id_tree::proof::Proof,
    pub(crate) cur_obj_id: ObjId,
    pub(crate) merkle_proofs: HashMap<Height, MerkleProof>,
}
