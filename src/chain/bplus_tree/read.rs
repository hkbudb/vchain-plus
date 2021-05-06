use super::{
    proof::{sub_proof::SubProof, Proof},
    BPlusTreeNode, BPlusTreeNodeId, BPlusTreeNodeLoader,
};
use crate::{
    acc::{AccValue, Set},
    chain::{range::Range, traits::Num, MAX_FANOUT, PUB_KEY},
    digest::{Digest, Digestible},
};
use anyhow::Result;
use smallvec::SmallVec;
use std::collections::VecDeque;

pub fn range_query<K: Num>(
    node_loader: impl BPlusTreeNodeLoader<K>,
    root_id: BPlusTreeNodeId,
    range: Range<K>,
) -> Result<(Set, AccValue, Proof<K>)> {
    let (res, acc, p) = inner_range_query(node_loader, root_id, range)?;
    Ok((res, acc, Proof::from_subproof(p)))
}

fn inner_range_query<K: Num>(
    node_loader: impl BPlusTreeNodeLoader<K>,
    root_id: BPlusTreeNodeId,
    range: Range<K>,
) -> Result<(Set, AccValue, SubProof<K>)> {
    use super::proof::{
        leaf::BPlusTreeLeaf, non_leaf::BPlusTreeNonLeaf, res_sub_tree::BPlusTreeResSubTree,
    };

    let mut query_res = Set::new();
    let mut res_acc_val: AccValue = AccValue::from_set(&query_res, &PUB_KEY);
    let mut query_proof = SubProof::from_hash(range, Digest::zero());

    let root_node = node_loader.load_node(root_id)?.unwrap();
    let cur_proof = &mut query_proof as *mut _;

    let mut queue: VecDeque<(BPlusTreeNode<K>, *mut SubProof<K>)> = VecDeque::new();
    queue.push_back((root_node, cur_proof));

    while let Some((cur_node, cur_proof_ptr)) = queue.pop_front() {
        match cur_node {
            BPlusTreeNode::Leaf(n) => {
                if range.is_in_range(n.num) {
                    // leaf
                    query_res = (&query_res) | (&n.data_set);
                    res_acc_val = res_acc_val + n.data_set_acc;
                    unsafe {
                        *cur_proof_ptr =
                            SubProof::from_leaf(BPlusTreeLeaf::new(n.num, n.data_set_acc));
                    }
                } else {
                    // hash(sub_tree)
                    unsafe {
                        *cur_proof_ptr =
                            SubProof::from_hash(Range::new(n.num, n.num), n.to_digest());
                    }
                }
            }
            BPlusTreeNode::NonLeaf(n) => {
                if n.range.is_covered(range) {
                    //res_node
                    query_res = (&query_res) | (&n.data_set);
                    res_acc_val = res_acc_val + n.data_set_acc;
                    unsafe {
                        *cur_proof_ptr = SubProof::from_res_sub_tree(BPlusTreeResSubTree::new(
                            n.range,
                            n.data_set_acc,
                            n.to_digest(),
                        ));
                    }
                } else if n.range.has_no_intersection(range) {
                    // hash(sub_tree)
                    unsafe {
                        *cur_proof_ptr = SubProof::from_hash(n.range, n.to_digest());
                    }
                } else if n.range.intersects(range) {
                    // non_leaf
                    let mut cur_proof_children =
                        SmallVec::<[Option<Box<SubProof<K>>>; MAX_FANOUT]>::new();

                    for child_id in &n.child_ids {
                        let child_node = node_loader.load_node(*child_id)?.unwrap();
                        let mut sub_proof = match &child_node {
                            BPlusTreeNode::Leaf(n) => Box::new(SubProof::from_hash(
                                Range::new(n.num, n.num),
                                n.to_digest(),
                            )),
                            BPlusTreeNode::NonLeaf(n) => {
                                Box::new(SubProof::from_hash(n.range, n.to_digest()))
                            }
                        };

                        let sub_proof_ptr = sub_proof.as_mut() as *mut _;
                        cur_proof_children.push(Some(sub_proof));
                        queue.push_back((child_node, sub_proof_ptr));
                    }
                    unsafe {
                        *cur_proof_ptr = SubProof::from_non_leaf(BPlusTreeNonLeaf::from_hashes(
                            n.range,
                            n.data_set_acc,
                            cur_proof_children,
                        ));
                    }
                } else {
                    println!("range not correct");
                }
            }
        }
    }
    Ok((query_res, res_acc_val, query_proof))
}
