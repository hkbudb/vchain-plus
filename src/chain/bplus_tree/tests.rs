use super::{
    super::tests::PUB_KEY,
    proof::sub_proof::SubProof,
    read::range_query,
    write::{Apply, WriteContext},
    BPlusTreeNode, BPlusTreeNodeId, BPlusTreeNodeLoader,
};
use crate::chain::id_tree::ObjId;
use crate::{chain::bplus_tree::BPlusTreeRoot, utils::init_tracing_subscriber};
use crate::{
    chain::{range::Range, traits::Num},
    digest::{Digest, Digestible},
};
use anyhow::{bail, Result};
use rand::Rng;
use std::collections::VecDeque;
use std::collections::{BTreeMap, HashMap};
use std::num::NonZeroU16;

#[derive(Debug, Default, Clone, Eq, PartialEq)]
struct TestBPlusTree<K: Num> {
    root_id: Option<BPlusTreeNodeId>,
    nodes: HashMap<BPlusTreeNodeId, BPlusTreeNode<K>>,
}

impl<K: Num> BPlusTreeNodeLoader<K> for TestBPlusTree<K> {
    fn load_node(&self, id: BPlusTreeNodeId) -> Result<BPlusTreeNode<K>> {
        match self.nodes.get(&id).cloned() {
            Some(n) => Ok(n),
            None => bail!("Cannot find node in TestBPlusTree"),
        }
    }
}

impl<K: Num> BPlusTreeNodeLoader<K> for &'_ TestBPlusTree<K> {
    fn load_node(&self, id: BPlusTreeNodeId) -> Result<BPlusTreeNode<K>> {
        match self.nodes.get(&id).cloned() {
            Some(n) => Ok(n),
            None => bail!("Cannot find node in TestBPlusTree"),
        }
    }
}

impl<K: Num> TestBPlusTree<K> {
    pub fn new() -> Self {
        Self {
            root_id: None,
            nodes: HashMap::new(),
        }
    }

    fn apply(&mut self, apply: Apply<K>) {
        self.root_id = apply.root.bplus_tree_root_id;
        self.nodes.extend(apply.nodes.into_iter());
    }
}

const FANOUT: u8 = 4;

fn get_dataset() -> (Vec<u32>, Vec<NonZeroU16>) {
    // 30 int from 1 to 25 with duplicates
    let keys: Vec<u32> = vec![
        9, 11, 23, 13, 4, 12, 5, 11, 10, 18, 20, 3, 24, 4, 15, 8, 7, 2, 3, 21, 1, 17, 6, 20, 14,
        25, 22, 16, 19, 1,
    ];

    // 30 ids
    unsafe {
        let ids: Vec<NonZeroU16> = vec![
            NonZeroU16::new_unchecked(1),
            NonZeroU16::new_unchecked(2),
            NonZeroU16::new_unchecked(3),
            NonZeroU16::new_unchecked(4),
            NonZeroU16::new_unchecked(5),
            NonZeroU16::new_unchecked(6),
            NonZeroU16::new_unchecked(7),
            NonZeroU16::new_unchecked(8),
            NonZeroU16::new_unchecked(9),
            NonZeroU16::new_unchecked(10),
            NonZeroU16::new_unchecked(11),
            NonZeroU16::new_unchecked(12),
            NonZeroU16::new_unchecked(13),
            NonZeroU16::new_unchecked(14),
            NonZeroU16::new_unchecked(15),
            NonZeroU16::new_unchecked(16),
            NonZeroU16::new_unchecked(17),
            NonZeroU16::new_unchecked(18),
            NonZeroU16::new_unchecked(19),
            NonZeroU16::new_unchecked(20),
            NonZeroU16::new_unchecked(21),
            NonZeroU16::new_unchecked(22),
            NonZeroU16::new_unchecked(23),
            NonZeroU16::new_unchecked(24),
            NonZeroU16::new_unchecked(25),
            NonZeroU16::new_unchecked(26),
            NonZeroU16::new_unchecked(27),
            NonZeroU16::new_unchecked(28),
            NonZeroU16::new_unchecked(29),
            NonZeroU16::new_unchecked(30),
        ];
        (keys, ids)
    }
}

pub fn set_root_id(bplus_tree_root: &mut BPlusTreeRoot, id: Option<BPlusTreeNodeId>) {
    bplus_tree_root.bplus_tree_root_id = id;
}

#[test]
fn test_read() {
    // K is u32
    let mut test_b_tree = TestBPlusTree::<u32>::new();
    let mut test_b_tree_root = BPlusTreeRoot::default();
    set_root_id(&mut test_b_tree_root, test_b_tree.root_id);
    let mut ctx = WriteContext::new(&mut test_b_tree, test_b_tree_root);
    let keys: Vec<u32> = get_dataset().0;
    let ids: Vec<NonZeroU16> = get_dataset().1;

    for i in 0..30 {
        ctx.insert(keys[i], ObjId(ids[i]), FANOUT, &PUB_KEY)
            .unwrap();
    }

    let changes = ctx.changes();
    test_b_tree.apply(changes);

    let root_digest = test_b_tree
        .load_node(test_b_tree.root_id.unwrap())
        .unwrap()
        .to_digest();

    let query_range = Range::new(1, 4);
    let (_v, acc, p) =
        range_query(&test_b_tree, test_b_tree.root_id, query_range, &PUB_KEY).unwrap();

    let res_digest = p.verify(query_range, acc, &PUB_KEY).unwrap();
    assert_eq!(root_digest, res_digest);

    let query_range = Range::new(3, 10);
    let (_v, acc, p) =
        range_query(&test_b_tree, test_b_tree.root_id, query_range, &PUB_KEY).unwrap();
    let res_digest = p.verify(query_range, acc, &PUB_KEY).unwrap();
    assert_eq!(root_digest, res_digest);

    let query_range = Range::new(5, 30);
    let (_v, acc, p) =
        range_query(&test_b_tree, test_b_tree.root_id, query_range, &PUB_KEY).unwrap();
    let res_digest = p.verify(query_range, acc, &PUB_KEY).unwrap();
    assert_eq!(root_digest, res_digest);

    let query_range = Range::new(31, 40);
    let (_v, acc, p) =
        range_query(&test_b_tree, test_b_tree.root_id, query_range, &PUB_KEY).unwrap();
    let res_digest = p.verify(query_range, acc, &PUB_KEY).unwrap();
    assert_eq!(root_digest, res_digest);
}

#[test]
fn test_insert_rich() {
    let mut test_b_tree = TestBPlusTree::<u32>::new();
    let mut test_b_tree_root = BPlusTreeRoot::default();
    set_root_id(&mut test_b_tree_root, test_b_tree.root_id);
    let mut ctx = WriteContext::new(&mut test_b_tree, test_b_tree_root);
    for _i in 0..6000 {
        let mut rng = rand::thread_rng();
        let v: u32 = rng.gen_range(0..3000);
        unsafe {
            ctx.insert(
                v,
                ObjId(NonZeroU16::new_unchecked(1 as u16)),
                FANOUT,
                &PUB_KEY,
            )
            .unwrap();
        }
    }
}

// time consuming test, ignored
#[test]
#[ignore]
fn test_update_rich() {
    init_tracing_subscriber("info").unwrap();
    let blk_size = 4;
    let time_win_size = 4;
    let blk_num = 30000;
    let mut test_b_tree = TestBPlusTree::<u32>::new();
    let mut test_b_tree_root = BPlusTreeRoot::default();
    set_root_id(&mut test_b_tree_root, test_b_tree.root_id);
    let mut ctx = WriteContext::new(&mut test_b_tree, test_b_tree_root);
    let mut db = BTreeMap::<u32, Vec<u32>>::new();
    let mut rng = rand::thread_rng();
    let mut obj_id: u16 = 1;
    info!("creating blocks...");
    for i in 0..blk_num {
        let mut vec = Vec::<u32>::new();
        for _ in 0..blk_size {
            vec.push(rng.gen_range(1..100));
        }
        db.insert(i, vec);
    }

    info!("start building blocks");
    for i in 0..blk_num {
        info!("building blk with blk id: {}", i);
        if i > time_win_size {
            // delete
            let vec = db.get(&(i - time_win_size)).unwrap();
            for key in vec {
                info!("delete key {}", key);
                if obj_id == 0 {
                    obj_id = 1;
                }
                unsafe {
                    ctx.delete(
                        *key,
                        ObjId(NonZeroU16::new_unchecked(obj_id as u16)),
                        FANOUT,
                        &PUB_KEY,
                    )
                    .unwrap();
                }
                obj_id = (obj_id + 1) % 35;
            }
        }

        // insert
        let vec = db.get(&i).unwrap();
        for key in vec {
            info!("insert key {}", key);
            if obj_id == 0 {
                obj_id = 1;
            }
            unsafe {
                ctx.insert(
                    *key,
                    ObjId(NonZeroU16::new_unchecked(obj_id as u16)),
                    FANOUT,
                    &PUB_KEY,
                )
                .unwrap();
            }
            obj_id = (obj_id + 1) % 35;
        }
    }
    let changes = ctx.changes();
    test_b_tree.apply(changes);
    assert_eq!(1, 1);
}

#[test]
fn test_delete_bug() {
    let mut test_b_tree = TestBPlusTree::<u32>::new();
    let mut test_b_tree_root = BPlusTreeRoot::default();
    set_root_id(&mut test_b_tree_root, test_b_tree.root_id);
    let mut ctx = WriteContext::new(&mut test_b_tree, test_b_tree_root);
    unsafe {
        ctx.insert(
            1,
            ObjId(NonZeroU16::new_unchecked(1 as u16)),
            FANOUT,
            &PUB_KEY,
        )
        .unwrap();
        ctx.insert(
            3,
            ObjId(NonZeroU16::new_unchecked(1 as u16)),
            FANOUT,
            &PUB_KEY,
        )
        .unwrap();
        ctx.insert(
            5,
            ObjId(NonZeroU16::new_unchecked(1 as u16)),
            FANOUT,
            &PUB_KEY,
        )
        .unwrap();
        ctx.insert(
            7,
            ObjId(NonZeroU16::new_unchecked(1 as u16)),
            FANOUT,
            &PUB_KEY,
        )
        .unwrap();
        ctx.insert(
            9,
            ObjId(NonZeroU16::new_unchecked(1 as u16)),
            FANOUT,
            &PUB_KEY,
        )
        .unwrap();
        ctx.insert(
            2,
            ObjId(NonZeroU16::new_unchecked(1 as u16)),
            FANOUT,
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            9,
            ObjId(NonZeroU16::new_unchecked(1 as u16)),
            FANOUT,
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            1,
            ObjId(NonZeroU16::new_unchecked(1 as u16)),
            FANOUT,
            &PUB_KEY,
        )
        .unwrap();
    }
    let changes = ctx.changes();
    test_b_tree.apply(changes);
    assert_eq!(1, 1);
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
