use super::{
    write::{Apply, WriteContext},
    BPlusTreeNode, BPlusTreeNodeId, BPlusTreeNodeLoader,
};
use crate::{
    acc::set::Set,
    chain::traits::Num,
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
}

#[test]
fn test_write() {
    // K is u32
    let mut test_b_tree = TestBPlusTree::<u32>::new();
    let mut ctx = WriteContext::new(&test_b_tree, test_b_tree.root_id);
    let mut keys: Vec<u32> = vec![
        16, 5, 25, 2, 21, 3, 12, 14, 7, 9, 24, 8, 19, 22, 23, 4, 15, 18, 1, 20, 11, 6, 13, 17, 10,
    ];
    let mut sets: Vec<Set> = vec![
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
    ];

    for i in 0..25 {
        //println!("inserting {}!!!", keys[i]);
        let _res = ctx.insert(keys[i], sets[i].clone());
    }
    let changes = ctx.changes();
    test_b_tree.apply(changes);

    println!("{:#?}", test_b_tree);
    assert_eq!(0, 1);
}

