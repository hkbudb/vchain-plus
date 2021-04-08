use super::IDTREE_FANOUT;
use crate::{
    create_id_type,
    digest::{Digest, Digestible},
};
use anyhow::Result;
use serde::{Deserialize, Serialize};
create_id_type!(IdTreeNodeId);
create_id_type!(IdTreeObjId);

pub mod read;
pub use read::*;
pub mod write;
pub use write::*;
pub mod proof;
pub use proof::*;
pub mod hash;
pub use hash::*;
pub mod tests;
pub use tests::*;

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum IdTreeNode {
    Leaf(IdTreeLeafNode),
    NonLeaf(IdTreeNonLeafNode),
}

impl IdTreeNode {
    pub fn get_node_id(&self) -> IdTreeNodeId {
        match self {
            IdTreeNode::Leaf(n) => n.id,
            IdTreeNode::NonLeaf(n) => n.id,
        }
    }

    pub fn from_leaf(l: IdTreeLeafNode) -> Self {
        Self::Leaf(l)
    }

    pub fn from_non_leaf(n: IdTreeNonLeafNode) -> Self {
        Self::NonLeaf(n)
    }
}

impl Digestible for IdTreeNode {
    fn to_digest(&self) -> Digest {
        match self {
            IdTreeNode::Leaf(n) => n.to_digest(),
            IdTreeNode::NonLeaf(n) => n.to_digest(),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct IdTreeLeafNode {
    pub id: IdTreeNodeId,
    pub obj_id: IdTreeObjId,
    pub obj_hash: Digest,
}

impl IdTreeLeafNode {
    fn new(obj_id: IdTreeObjId, obj_hash: Digest) -> Self {
        Self {
            id: IdTreeNodeId::next_id(),
            obj_id,
            obj_hash,
        }
    }

    fn new_dbg(id: IdTreeNodeId, obj_id: IdTreeObjId, obj_hash: Digest) -> Self {
        Self {
            id,
            obj_id,
            obj_hash,
        }
    }
}

impl Digestible for IdTreeLeafNode {
    fn to_digest(&self) -> Digest {
        id_tree_leaf_hash(self.obj_id, &self.obj_hash)
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct IdTreeNonLeafNode {
    pub id: IdTreeNodeId,
    pub child_hashes: [Digest; IDTREE_FANOUT],
    pub child_ids: [IdTreeNodeId; IDTREE_FANOUT],
}

impl IdTreeNonLeafNode {
    pub fn new(
        child_hashes: [Digest; IDTREE_FANOUT],
        child_ids: [IdTreeNodeId; IDTREE_FANOUT],
    ) -> Self {
        Self {
            id: IdTreeNodeId::next_id(),
            child_hashes,
            child_ids,
        }
    }

    pub fn new_dbg(
        id: IdTreeNodeId,
        child_hashes: [Digest; IDTREE_FANOUT],
        child_ids: [IdTreeNodeId; IDTREE_FANOUT],
    ) -> Self {
        Self {
            id,
            child_hashes,
            child_ids,
        }
    }

    pub fn new_ept() -> Self {
        Self {
            id: IdTreeNodeId::next_id(),
            child_hashes: [Digest::zero(); IDTREE_FANOUT],
            child_ids: [IdTreeNodeId(0); IDTREE_FANOUT],
        }
    }

    pub fn get_child_id(&self, idx: usize) -> Option<&IdTreeNodeId> {
        self.child_ids.get(idx)
    }

    pub fn get_child_id_mut(&mut self, idx: usize) -> Option<&mut IdTreeNodeId> {
        self.child_ids.get_mut(idx)
    }

    pub fn get_child_hash(&self, idx: usize) -> Option<&Digest> {
        self.child_hashes.get(idx)
    }

    pub fn get_child_hash_mut(&mut self, idx: usize) -> Option<&mut Digest> {
        self.child_hashes.get_mut(idx)
    }
}

impl Digestible for IdTreeNonLeafNode {
    fn to_digest(&self) -> Digest {
        id_tree_non_leaf_hash(self.child_hashes.iter())
    }
}

pub trait IdTreeNodeLoader {
    fn load_node(&self, id: IdTreeNodeId) -> Result<Option<IdTreeNode>>;
}

/*
pub fn update_id_tree<K: Num>(
    n: u64, // # obj per blk
    k: u64, // max k
    cur_blk_id: BlockId,
    raw_obj_ids: impl Iterator<Item = ObjId>,
    chain: &mut (impl ReadInterface<K> + WriteInterface<K>),
) -> Result<IdTreeNode> {
    let obj_ids: Vec<IdTreeObjId> = raw_obj_ids
        .map(|o| IdTreeObjId(o.unwrap() % (n * k)))
        .collect();
    let pre_blk_id: BlockId = BlockId(cur_blk_id.unwrap() - 1);
    let pre_root_id: IdTreeNodeId = chain.read_block_content(pre_blk_id)?.id_tree_root_id;
    let mut id_tree_root: IdTreeNode = IdTreeNode::NonLeaf(IdTreeNonLeafNode::new(
        IdTreeNodeId::next_id(),
        SmallVec::<[Digest; IDTREE_FANOUT]>::new(),
        SmallVec::<[IdTreeNodeId; IDTREE_FANOUT]>::new(),
    )); // the root of the new id tree

    /* step i -- create partial tree */
    for obj_id in obj_ids {
        let mut path: Vec<usize> = Vec::new();
        let depth: u64 = ((((k * n) as f64).log(IDTREE_FANOUT as f64)).ceil() + (1 as f64)) as u64;
        fanout_nary(obj_id.unwrap(), IDTREE_FANOUT as u64, depth, &mut path);

        let mut index: usize = 0;
        let mut tmp_node: IdTreeNode;
        let mut cur_node: &mut IdTreeNode = &mut id_tree_root;

        while path.len() > 1 {
            if let Some(i) = path.pop() {
                index = i;
            }
            match if let IdTreeNode::NonLeaf(n) = cur_node {
                n.child_ids.get(index)
            } else {
                None
            } {
                None => {
                    let node = IdTreeNonLeafNode::new(
                        IdTreeNodeId::next_id(),
                        SmallVec::<[Digest; IDTREE_FANOUT]>::new(),
                        SmallVec::<[IdTreeNodeId; IDTREE_FANOUT]>::new(),
                    );

                    if let IdTreeNode::NonLeaf(n) = cur_node {
                        n.child_ids[index] = node.id;
                    }

                    chain.write_id_tree_node(IdTreeNode::NonLeaf(node))?;
                }
                Some(_) => {}
            }
            let mut id: IdTreeNodeId = IdTreeNodeId(0);
            if let IdTreeNode::NonLeaf(n) = cur_node {
                id = n.child_ids[index];
            }
            tmp_node = chain.read_id_tree_node(id)?;
            cur_node = &mut tmp_node;
        }

        if path.len() == 1 {
            if let Some(i) = path.pop() {
                index = i;
            }
            let node = IdTreeLeafNode::new(IdTreeNodeId::next_id(), obj_id, {
                let mut state = blake2().to_state();
                state.update(&obj_id.to_le_bytes());
                Digest::from(state.finalize())
            });
            if let IdTreeNode::NonLeaf(n) = cur_node {
                n.child_ids[index] = node.id;
            }
            chain.write_id_tree_node(IdTreeNode::Leaf(node))?;
        }
    }

    /* step ii -- update partial tree */
    update_id_hash(pre_root_id, id_tree_root.get_node_id(), chain)?;

    Ok(id_tree_root)
}


// update id & hash for new partial tree
fn update_id_hash<K: Num>(
    cur_id: IdTreeNodeId,
    cur_id_pre: IdTreeNodeId,
    chain: &mut (impl ReadInterface<K> + WriteInterface<K>),
) -> Result<()> {
    let mut cur_node: &mut IdTreeNode = &mut chain.read_id_tree_node(cur_id)?;
    let cur_node_pre: &IdTreeNode = &chain.read_id_tree_node(cur_id_pre)?;
    for i in 0..IDTREE_FANOUT {
        match if let IdTreeNode::NonLeaf(n) = cur_node {
            n.child_ids.get(i)
        } else {
            None
        } {
            None => {
                if let (IdTreeNode::NonLeaf(n), IdTreeNode::NonLeaf(n_pre)) =
                    (&mut cur_node, &cur_node_pre)
                {
                    n.child_ids[i] = n_pre.child_ids[i];
                    n.child_hashes[i] = chain.read_id_tree_node(n_pre.child_ids[i])?.to_digest();
                }
            }
            Some(child_id) => {
                if let IdTreeNode::Leaf(_l) = chain.read_id_tree_node(*child_id)? {
                    if let IdTreeNode::NonLeaf(n) = cur_node {
                        n.child_hashes[i] = chain.read_id_tree_node(n.child_ids[i])?.to_digest();
                    }
                } else {
                    if let (IdTreeNode::NonLeaf(n), IdTreeNode::NonLeaf(n_pre)) =
                        (&mut cur_node, &cur_node_pre)
                    {
                        update_id_hash(n_pre.child_ids[i], n.child_ids[i], chain)?;
                    }
                }
            }
        }
    }

    Ok(())
}

pub fn query_id_tree<K: Num>(
    nk: u64,         // n*k
    blk_id: BlockId, // end block id
    raw_obj_ids: impl Iterator<Item = ObjId>,
    chain: &mut (impl ReadInterface<K> + WriteInterface<K>),
) -> Result<(Vec<Option<Digest>>, Proof)> {
    let obj_ids: Vec<IdTreeObjId> = raw_obj_ids.map(|o| IdTreeObjId(o.unwrap() % nk)).collect();
    let root_id: IdTreeNodeId = chain.read_block_content(blk_id)?.id_tree_root_id;
    let root_node: &IdTreeNode = &chain.read_id_tree_node(root_id)?;

    let mut results: Vec<Option<Digest>> = Vec::new();
    let mut sub_proof: SubProof = SubProof::default();
    let depth: u64 = ((((nk) as f64).log(IDTREE_FANOUT as f64)).ceil() + (1 as f64)) as u64;

    let first_res = inner_query_id_tree(depth, obj_ids[0], root_node, chain);
    results.push(first_res.unwrap().0);
    sub_proof = first_res.unwrap().1;
    obj_ids.pop();

    for obj_id in obj_ids {
        let result_with_proof = inner_query_id_tree(depth, obj_id, root_node, chain);
        sub_proof = merge_sub_proof(&sub_proof, &result_with_proof.unwrap().1);
    }
    Ok((results, Proof::from_subproof(sub_proof)))
}

// query a single id
fn inner_query_id_tree<K: Num>(
    depth: u64,
    obj_id: IdTreeObjId,
    root_node: &IdTreeNode,
    chain: &mut (impl ReadInterface<K> + WriteInterface<K>),
) -> Result<(Option<Digest>, SubProof)> {
    let mut cur_path: Vec<usize> = Vec::new();
    fanout_nary(obj_id.unwrap(), IDTREE_FANOUT as u64, depth, &mut cur_path);
    let mut sub_proof: SubProof = SubProof::from_hash(root_node.to_digest());
    let mut obj_hash: Option<Digest>;

    let mut cur_node = root_node;
    let mut cur_proof = &mut sub_proof as *mut _;

    loop {
        match cur_node {
            IdTreeNode::Leaf(n) => {
                obj_hash = if obj_id == n.obj_id {
                    Some(n.obj_hash.clone())
                } else {
                    None
                };
                unsafe {
                    *cur_proof = SubProof::from_leaf(IdTreeLeaf::new(n.obj_hash.clone()));
                }
                break;
            }
            IdTreeNode::NonLeaf(n) => {
                let child_idx = cur_path.pop().unwrap();
                let id_opt = n.child_ids.get(child_idx);
                match id_opt {
                    Some(id) => {
                        if let child = chain.read_id_tree_node(*id)? {
                            let mut child_sub_proof =
                                Box::new(SubProof::from_hash(child.to_digest()));
                            let child_sub_proof_ptr = &mut *child_sub_proof as *mut _;
                            let mut non_leaf = IdTreeNonLeaf::from_hashes(&n.child_hashes);
                            *non_leaf.get_child_mut(child_idx) = Some(child_sub_proof);
                            unsafe {
                                *cur_proof = SubProof::from_non_leaf(non_leaf);
                            }
                            cur_node = &child;
                            cur_proof = child_sub_proof_ptr;
                            continue;
                        }
                    }
                    None => {}
                };

                let non_leaf = IdTreeNonLeaf::from_hashes(&n.child_hashes);
                unsafe {
                    *cur_proof = SubProof::from_non_leaf(non_leaf);
                }
                break;
            }
        }
    }

    Ok((obj_hash, sub_proof))
}

// merge proof
fn merge_sub_proof(p1: &SubProof, p2: &SubProof) -> SubProof {
    let mut merged_proof: SubProof;
    match (p1, p2) {
        (SubProof::Leaf(_), SubProof::Leaf(_)) => {
            // will not happen
        }
        (SubProof::Leaf(_), SubProof::NonLeaf(_)) => {
            // will not happen
        }
        (SubProof::NonLeaf(_), SubProof::Leaf(_)) => {
            // will not happen
        }
        (SubProof::Hash(h1), SubProof::Hash(h2)) => {
            merged_proof = *p1;
        }
        (SubProof::Hash(h), SubProof::Leaf(l)) => {
            merged_proof = *p2;
        }
        (SubProof::Leaf(l), SubProof::Hash(h)) => {
            merged_proof = *p1;
        }
        (SubProof::Hash(h), SubProof::NonLeaf(n)) => {
            merged_proof = *p2;
        }
        (SubProof::NonLeaf(n), SubProof::Hash(h)) => {
            merged_proof = *p1;
        }
        (SubProof::NonLeaf(n1), SubProof::NonLeaf(n2)) => {
            let mut non_leaf = IdTreeNonLeaf::default();
            for i in 0..IDTREE_FANOUT {
                let a = n1.get_child(i);
                let b = n2.get_child(i);
                match (a, b) {
                    (Some(n1), Some(n2)) => {
                        non_leaf.set_child(i, merge_sub_proof(n1, n2));
                    }
                    (_, _) => {}
                }
            }
            merged_proof = SubProof::from_non_leaf(non_leaf);
        }
    }
    merged_proof
}
*/
