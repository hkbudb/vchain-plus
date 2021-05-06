#![allow(unused)]
use super::{
    proof::sub_proof::SubProof,
    read::range_query,
    write::{Apply, WriteContext},
    BPlusTreeLeafNode, BPlusTreeNode, BPlusTreeNodeId, BPlusTreeNodeLoader, BPlusTreeNonLeafNode,
};
use crate::{
    acc::{AccValue, Set},
    chain::{id_tree::IdTreeObjId, range::Range, traits::Num, MAX_FANOUT, PUB_KEY},
    digest::{Digest, Digestible},
    set,
};

use anyhow::Result;
use smallvec::SmallVec;
use std::collections::HashMap;
use std::collections::VecDeque;

#[derive(Debug, Default, Clone, Eq, PartialEq)]
struct TestBPlusTree<K: Num> {
    root_id: BPlusTreeNodeId,
    nodes: HashMap<BPlusTreeNodeId, BPlusTreeNode<K>>,
}

impl<K: Num> BPlusTreeNodeLoader<K> for TestBPlusTree<K> {
    fn load_node(&self, id: BPlusTreeNodeId) -> Result<Option<BPlusTreeNode<K>>> {
        match self.nodes.get(&id).cloned() {
            Some(n) => Ok(Some(n)),
            None => Ok(None),
        }
    }
}

impl<K: Num> BPlusTreeNodeLoader<K> for &'_ TestBPlusTree<K> {
    fn load_node(&self, id: BPlusTreeNodeId) -> Result<Option<BPlusTreeNode<K>>> {
        match self.nodes.get(&id).cloned() {
            Some(n) => Ok(Some(n)),
            None => Ok(None),
        }
    }
}

impl<K: Num> TestBPlusTree<K> {
    pub fn new() -> Self {
        Self {
            root_id: BPlusTreeNodeId::next_id(),
            nodes: HashMap::new(),
        }
    }

    fn apply(&mut self, apply: Apply<K>) {
        self.root_id = apply.root_id;
        self.nodes.extend(apply.nodes.into_iter());
    }

    fn search(&self, key: K) -> bool {
        let mut res = false;
        for (_n_id, n) in &self.nodes {
            match n {
                BPlusTreeNode::Leaf(n) => {
                    if n.num == key {
                        res = true;
                        break;
                    } else {
                        println!("key is {:?}, but the node has val {:?}", key, n.num);
                    }
                }
                BPlusTreeNode::NonLeaf(n) => {
                    continue;
                }
            }
        }
        println!("the search res for key {:?} is: {}", key, res);
        res
    }
}

fn get_dataset() -> (Vec<u32>, Vec<u64>) {
    // 25 unique int from 1 to 25
    // let keys: Vec<u32> = vec![
    //     16, 5, 25, 2, 21, 3, 12, 14, 7, 9, 24, 8, 19, 22, 23, 4, 15, 18, 1, 20, 11, 6, 13, 17, 10,
    // ];

    // 30 int from 1 to 25 with duplicates
    let keys: Vec<u32> = vec![
        9, 11, 23, 13, 4, 12, 5, 11, 10, 18, 20, 3, 24, 4, 15, 8, 7, 2, 3, 21, 1, 17, 6, 20, 14,
        25, 22, 16, 19, 1,
    ];

    // 30 unique int from 1 to 30
    // let keys: Vec<u32> = vec![
    //     1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    //     26, 27, 28, 29, 30,
    // ];

    // 30 ids
    let ids: Vec<u64> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 30,
    ];
    (keys, ids)
}

#[test]
fn test_read() {
    // K is u32
    let mut test_b_tree = TestBPlusTree::<u32>::new();
    let mut ctx = WriteContext::new(&test_b_tree, test_b_tree.root_id);
    let keys: Vec<u32> = get_dataset().0;
    let ids: Vec<u64> = get_dataset().1;

    for i in 0..30 {
        let _res = ctx.insert(keys[i], IdTreeObjId(ids[i]));
    }
    // let _res = ctx.delete(14, IdTreeObjId(25), MAX_FANOUT);
    // let _res = ctx.delete(13, IdTreeObjId(4), MAX_FANOUT);
    // let _res = ctx.delete(9, IdTreeObjId(1), MAX_FANOUT);
    // let _res = ctx.delete(6, IdTreeObjId(23), MAX_FANOUT);
    // let _res = ctx.delete(10, IdTreeObjId(9), MAX_FANOUT);
    // let _res = ctx.delete(9, IdTreeObjId(1), MAX_FANOUT);
    // let _res = ctx.delete(8, IdTreeObjId(16), MAX_FANOUT);

    let changes = ctx.changes();
    test_b_tree.apply(changes);

    let query_range = Range::new(1, 4);
    let (v, acc, p) = range_query(&test_b_tree, test_b_tree.root_id, query_range).unwrap();
    p.verify(
        test_b_tree
            .load_node(test_b_tree.root_id)
            .unwrap()
            .unwrap()
            .to_digest(),
        query_range,
        acc,
    );

    let query_range = Range::new(3, 10);
    let (v, acc, p) = range_query(&test_b_tree, test_b_tree.root_id, query_range).unwrap();
    p.verify(
        test_b_tree
            .load_node(test_b_tree.root_id)
            .unwrap()
            .unwrap()
            .to_digest(),
        query_range,
        acc,
    );

    let query_range = Range::new(5, 30);
    let (v, acc, p) = range_query(&test_b_tree, test_b_tree.root_id, query_range).unwrap();
    p.verify(
        test_b_tree
            .load_node(test_b_tree.root_id)
            .unwrap()
            .unwrap()
            .to_digest(),
        query_range,
        acc,
    );

    assert_eq!(1, 1);
}

fn build_test_bplus_tree0() -> TestBPlusTree<u32> {
    let mut bplus_tree: TestBPlusTree<u32> = TestBPlusTree::default();
    let leaf1 = BPlusTreeLeafNode::new_dbg(BPlusTreeNodeId(3), 9 as u32, set! {1});
    let leaf1_id = leaf1.id;
    bplus_tree
        .nodes
        .insert(leaf1_id, BPlusTreeNode::Leaf(leaf1));
    bplus_tree.root_id = leaf1_id;
    bplus_tree
}

fn build_test_bplus_tree1() -> TestBPlusTree<u32> {
    let mut bplus_tree: TestBPlusTree<u32> = TestBPlusTree::default();
    let leaf1 = BPlusTreeLeafNode::new_dbg(BPlusTreeNodeId(11), 9 as u32, set! {1});
    let leaf1_id = leaf1.id;
    let leaf1_hash = leaf1.to_digest();
    bplus_tree
        .nodes
        .insert(leaf1_id, BPlusTreeNode::Leaf(leaf1));

    let leaf2 = BPlusTreeLeafNode::new_dbg(BPlusTreeNodeId(12), 11 as u32, set! {2});
    let leaf2_id = leaf2.id;
    let leaf2_hash = leaf2.to_digest();
    bplus_tree
        .nodes
        .insert(leaf2_id, BPlusTreeNode::Leaf(leaf2));

    let mut non_leaf1_child_ids = SmallVec::<[BPlusTreeNodeId; MAX_FANOUT]>::new();
    non_leaf1_child_ids.push(leaf1_id);
    non_leaf1_child_ids.push(leaf2_id);
    let mut non_leaf1_child_hashes = SmallVec::<[Digest; MAX_FANOUT]>::new();
    non_leaf1_child_hashes.push(leaf1_hash);
    non_leaf1_child_hashes.push(leaf2_hash);
    let non_leaf1_set = set! {1, 2};
    let non_leaf1_set_acc = AccValue::from_set(&non_leaf1_set, &PUB_KEY);
    let non_leaf1 = BPlusTreeNonLeafNode::new_dbg(
        BPlusTreeNodeId(10),
        Range::new(9, 11),
        non_leaf1_set,
        non_leaf1_set_acc,
        non_leaf1_child_hashes,
        non_leaf1_child_ids,
    );
    let non_leaf1_id = non_leaf1.id;
    bplus_tree
        .nodes
        .insert(non_leaf1_id, BPlusTreeNode::NonLeaf(non_leaf1));
    bplus_tree.root_id = non_leaf1_id;

    bplus_tree
}

#[test]
#[ignore]
fn test_write() {
    // BPlusTreeNodeId increase conflicts with read_test
    // two tests should not be conducted at the same time
    let keys: Vec<u32> = get_dataset().0;
    let ids: Vec<u64> = get_dataset().1;

    let mut test_b_tree0 = TestBPlusTree::<u32>::new();
    let mut ctx0 = WriteContext::new(&test_b_tree0, test_b_tree0.root_id);
    for i in 0..1 {
        let _res = ctx0.insert(keys[i], IdTreeObjId(ids[i]));
    }
    let changes0 = ctx0.changes();
    test_b_tree0.apply(changes0);
    assert_eq!(test_b_tree0, build_test_bplus_tree0());

    let mut test_b_tree1 = TestBPlusTree::<u32>::new();
    let mut ctx1 = WriteContext::new(&test_b_tree1, test_b_tree1.root_id);
    for i in 0..2 {
        let _res = ctx1.insert(keys[i], IdTreeObjId(ids[i]));
    }
    let changes1 = ctx1.changes();
    test_b_tree1.apply(changes1);
    assert_eq!(test_b_tree1, build_test_bplus_tree1());
}

#[test]
fn test_pointer() {
    let mut query_proof = SubProof::from_hash(Range::new(1, 2), Digest::zero());
    let mut cur_proof = &mut query_proof as *mut _;
    let mut sub_proof_queue: VecDeque<*mut SubProof<i32>> = VecDeque::new();
    sub_proof_queue.push_back(cur_proof);
    cur_proof = sub_proof_queue.pop_front().unwrap();
    println!("Raw pointer address before: {:p}", cur_proof);
    unsafe {
        *cur_proof = SubProof::from_hash(Range::new(2, 3), Digest::zero());
    }
    println!("Raw pointer address after: {:p}", cur_proof);
    assert_eq!(1, 1);
}

#[test]
#[ignore]
fn test_rich() {
    // time-consuming test, ignored
    let mut res = true;
    let mut test_b_tree = TestBPlusTree::<u32>::new();
    let mut ctx = WriteContext::new(&test_b_tree, test_b_tree.root_id);
    let upper_bound = 10000;
    for i in 0..upper_bound {
        let _res = ctx.insert(i, IdTreeObjId(i as u64));
    }
    let changes = ctx.changes();
    test_b_tree.apply(changes);

    println!("{:#?}", test_b_tree);

    for i in 0..upper_bound {
        res = res && test_b_tree.search(i);
        if !res {
            println!("failed in searching {}", i);
        }
    }
    assert_eq!(res, true);
}
