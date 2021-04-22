#![allow(unused)]
use super::{
    write::{Apply, WriteContext},
    BPlusTreeLeafNode, BPlusTreeNode, BPlusTreeNodeId, BPlusTreeNodeLoader, BPlusTreeNonLeafNode,
};
use crate::{
    acc::set::Set,
    chain::{range::Range, traits::Num, MAX_FANOUT},
    create_id_type,
    digest::{Digest, Digestible},
    set,
};
use anyhow::Result;
use smallvec::SmallVec;
use std::collections::{HashMap, HashSet};
create_id_type!(BPlusId);

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
        for (n_id, n) in &self.nodes {
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

fn get_dataset() -> (Vec<u32>, Vec<Set>) {
    // let keys: Vec<u32> = vec![
    //     16, 5, 25, 2, 21, 3, 12, 14, 7, 9, 24, 8, 19, 22, 23, 4, 15, 18, 1, 20, 11, 6, 13, 17, 10,
    // ];
    let keys: Vec<u32> = vec![
        9, 11, 23, 13, 4, 12, 5, 10, 18, 20, 3, 24, 15, 8, 7, 2, 21, 1, 17, 6, 14, 25, 22, 16, 19,
    ];
    // let keys: Vec<u32> = vec![
    //     1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    //     26, 27, 28, 29, 30,
    // ];
    // let keys: Vec<u32> = vec![1, 2, 4, 1, 3, 2, 4, 4, 1, 3, 3, 2];
    // let sets: Vec<Set> = vec![
    //     set! {1},
    //     set! {1},
    //     set! {1},
    //     set! {2},
    //     set! {1},
    //     set! {2},
    //     set! {2},
    //     set! {3},
    //     set! {3},
    //     set! {2},
    //     set! {3},
    //     set! {3},
    // ];

    let sets: Vec<Set> = vec![
        set! {1, 2},
        set! {1, 3},
        set! {2},
        set! {4, 5},
        set! {1, 3, 4},
        set! {5},
        set! {3, 5, 8},
        set! {8, 9},
        set! {6, 9},
        set! {4, 7},
        set! {2, 6},
        set! {4, 7, 8},
        set! {5, 3},
        set! {3, 8, 9},
        set! {2, 7, 4},
        set! {5, 2, 6},
        set! {7, 3},
        set! {10, 4},
        set! {2, 5, 8},
        set! {3, 6, 1},
        set! {7, 4, 2},
        set! {1, 4, 8, 3},
        set! {6, 2, 7, 9},
        set! {3},
        set! {1, 8},
        set! {1, 2},
        set! {1, 3},
        set! {2},
        set! {4, 5},
        set! {1, 3, 4},
    ];
    (keys, sets)
}

fn build_test_bplus_tree() -> TestBPlusTree<u32> {
    let mut keys: Vec<u32> = get_dataset().0;
    let mut sets: Vec<Set> = get_dataset().1;
    keys.reverse();
    sets.reverse();

    let mut bplus_tree: TestBPlusTree<u32> = TestBPlusTree::default();

    let leaf1 =
        BPlusTreeLeafNode::new_dbg(BPlusTreeNodeId(6), keys.pop().unwrap(), sets.pop().unwrap());
    let leaf1_id = leaf1.id;
    let leaf1_hash = leaf1.to_digest();
    bplus_tree
        .nodes
        .insert(leaf1_id, BPlusTreeNode::Leaf(leaf1));

    let leaf2 =
        BPlusTreeLeafNode::new_dbg(BPlusTreeNodeId(7), keys.pop().unwrap(), sets.pop().unwrap());
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
    let non_leaf1 = BPlusTreeNonLeafNode::new_dbg(
        BPlusTreeNodeId(5),
        Range::new(9, 11),
        set! {1, 2, 3},
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
fn test_write() {
    // K is u32
    let expect = build_test_bplus_tree();
    let mut test_b_tree = TestBPlusTree::<u32>::new();
    let mut ctx = WriteContext::new(&test_b_tree, test_b_tree.root_id);
    let keys: Vec<u32> = get_dataset().0;
    let sets: Vec<Set> = get_dataset().1;

    for i in 0..2 {
        let _res = ctx.insert(keys[i], sets[i].clone());
    }
    let changes = ctx.changes();
    test_b_tree.apply(changes);

    assert_eq!(test_b_tree, expect);
    println!("{:#?}", test_b_tree);
    println!("{:#?}", expect);
}

#[test]
#[ignore]
fn test_rich() {
    let mut res = true;
    let mut test_b_tree = TestBPlusTree::<u32>::new();
    let mut ctx = WriteContext::new(&test_b_tree, test_b_tree.root_id);
    let upper_bound = 10000;
    for i in 0..upper_bound {
        let _res = ctx.insert(i, set! {1});
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
