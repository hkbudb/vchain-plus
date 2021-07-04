use crate::{
    acc::{AccPublicKey, AccValue, Set},
    chain::trie_tree::{
        proof::{sub_proof::SubProof, Proof},
        split_at_common_prefix2, TrieNode, TrieNodeId, TrieNodeLoader,
    },
    digest::{Digest, Digestible},
};
use anyhow::{anyhow, bail, Result};
use std::collections::BTreeMap;

pub fn query_trie(
    node_loader: &impl TrieNodeLoader,
    root_id: Option<TrieNodeId>,
    keyword: String,
    pk: &AccPublicKey,
) -> Result<(Set, AccValue, Proof)> {
    let trie_root_id: TrieNodeId;
    match root_id {
        Some(id) => {
            trie_root_id = id;
        }
        None => bail!("The id tree is empty"),
    }

    let root_node = node_loader.load_node(trie_root_id)?;
    let (res, acc, p) = inner_query_trie(node_loader, trie_root_id, root_node, keyword, pk)?;
    Ok((res, acc, Proof::from_subproof(p)))
}

fn inner_query_trie(
    node_loader: &impl TrieNodeLoader,
    root_id: TrieNodeId,
    root_node: TrieNode,
    keyword: String,
    pk: &AccPublicKey,
) -> Result<(Set, AccValue, SubProof)> {
    use super::proof::{leaf::TrieLeaf, non_leaf::TrieNonLeaf};

    let mut query_proof = SubProof::from_hash(root_id, keyword.clone(), root_node.to_digest());
    let query_val: Set;
    let res_acc: AccValue;

    let mut cur_node = root_node;
    let mut cur_key = keyword;
    let mut cur_proof = &mut query_proof as *mut _;

    loop {
        match &cur_node {
            TrieNode::Leaf(n) => {
                if n.rest == cur_key {
                    query_val = n.data_set.clone();
                    res_acc = n.data_set_acc;
                    unsafe {
                        *cur_proof = SubProof::from_leaf(TrieLeaf::new(
                            n.id,
                            n.rest.clone(),
                            n.data_set_acc,
                        ));
                    }
                } else {
                    query_val = Set::new();
                    res_acc = AccValue::from_set(&query_val, pk);
                    unsafe {
                        *cur_proof = SubProof::from_hash(n.id, n.rest.clone(), n.to_digest());
                    }
                }
                break;
            }
            TrieNode::NonLeaf(n) => {
                let (_common_key, cur_idx, rest_cur_key, _node_idx, _rest_node_key) =
                    split_at_common_prefix2(&cur_key, &n.nibble);

                match n.children.get(&cur_idx) {
                    Some((id, hash)) => {
                        let sub_node = node_loader.load_node(*id)?;
                        let mut sub_proof =
                            Box::new(SubProof::from_hash(*id, rest_cur_key.clone(), *hash));
                        let sub_proof_ptr = &mut *sub_proof as *mut _;
                        let mut children = BTreeMap::new();
                        for (c, (i, h)) in &n.children {
                            let child_node = node_loader.load_node(*i)?;
                            children.insert(
                                *c,
                                Box::new(SubProof::from_hash(
                                    child_node.get_id(),
                                    child_node.get_string(),
                                    *h,
                                )),
                            );
                        }
                        let mut non_leaf = TrieNonLeaf::from_hashes(
                            (*n.nibble).to_string(),
                            n.data_set_acc,
                            children,
                        );
                        *non_leaf
                            .children
                            .get_mut(&cur_idx)
                            .ok_or_else(|| anyhow!("Cannot find subproof!"))? = sub_proof;
                        unsafe {
                            *cur_proof = SubProof::from_non_leaf(non_leaf);
                        }
                        cur_node = sub_node;
                        cur_proof = sub_proof_ptr;
                        cur_key = rest_cur_key;
                        continue;
                    }
                    None => {
                        query_val = Set::new();
                        res_acc = AccValue::from_set(&query_val, pk);
                        unsafe {
                            *cur_proof = SubProof::from_hash(n.id, n.nibble.clone(), n.to_digest());
                        }
                        break;
                    }
                }
            }
        }
    }

    Ok((query_val, res_acc, query_proof))
}

pub struct ReadContext<'a, L: TrieNodeLoader> {
    node_loader: &'a L,
    root_id: Option<TrieNodeId>,
    proof: Proof,
}

impl<'a, L: TrieNodeLoader> ReadContext<'a, L> {
    pub fn new(node_loader: &'a L, root_id: Option<TrieNodeId>) -> Self {
        match root_id {
            Some(id) => match node_loader.load_node(id) {
                Ok(n) => {
                    let nibble = n.get_string();
                    let dig = n.to_digest();
                    Self {
                        node_loader,
                        root_id,
                        proof: Proof::from_root_hash(id, nibble, dig),
                    }
                }
                Err(_) => Self {
                    node_loader,
                    root_id,
                    proof: Proof::from_root_hash(id, "".to_string(), Digest::zero()),
                },
            },
            None => Self {
                node_loader,
                root_id,
                proof: Proof::from_root_hash(TrieNodeId(0), "".to_string(), Digest::zero()),
            },
        }
    }

    pub fn get_proof(&self) -> &Proof {
        &self.proof
    }

    pub fn into_proof(self) -> Proof {
        self.proof
    }

    pub fn query(&mut self, keyword: String, pk: &AccPublicKey) -> Result<(Set, AccValue)> {
        let query_val: Set;
        let res_acc: AccValue;
        match self.proof.root.as_mut() {
            Some(root) => match root.search_prefix(keyword) {
                Some((sub_proof, sub_root_id, cur_key)) => {
                    let sub_root_node = self.node_loader.load_node(sub_root_id)?;
                    let (v, a, p) = inner_query_trie(
                        self.node_loader,
                        sub_root_id,
                        sub_root_node,
                        cur_key,
                        pk,
                    )?;
                    unsafe {
                        *sub_proof = p;
                    }
                    query_val = v;
                    res_acc = a;
                }
                None => {
                    query_val = Set::new();
                    res_acc = AccValue::from_set(&query_val, pk);
                }
            },
            None => {
                let (v, a, p) = query_trie(self.node_loader, self.root_id, keyword, pk)?;
                self.proof = p;
                query_val = v;
                res_acc = a;
            }
        }
        Ok((query_val, res_acc))
    }
}
