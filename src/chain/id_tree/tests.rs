use super::{
    read::{query_id_tree, query_without_proof, ReadContext},
    write::{Apply, WriteContext},
    IdTreeInternalId, IdTreeLeafNode, IdTreeNode, IdTreeNodeId, IdTreeNodeLoader,
    IdTreeNonLeafNode,
};
use crate::{
    chain::{
        block::Height,
        id_tree::{IdTreeRoot, ObjId},
        object::Object,
        MAX_ININE_ID_FANOUT,
    },
    digest::{blake2, Digest, Digestible},
};
use anyhow::{bail, Result};
use smallvec::SmallVec;
use std::{
    collections::{HashMap, HashSet},
    num::NonZeroU16,
};

fn create_id_tree_leaf(
    id: IdTreeNodeId,
    obj_id: IdTreeInternalId,
    obj_hash: Digest,
) -> IdTreeLeafNode {
    IdTreeLeafNode {
        id,
        obj_id,
        obj_hash,
    }
}

fn create_id_tree_non_leaf(
    id: IdTreeNodeId,
    child_hashes: SmallVec<[Digest; MAX_ININE_ID_FANOUT]>,
    child_ids: SmallVec<[IdTreeNodeId; MAX_ININE_ID_FANOUT]>,
) -> IdTreeNonLeafNode {
    IdTreeNonLeafNode {
        id,
        child_hashes,
        child_ids,
    }
}

#[derive(Debug, Default, Clone, Eq, PartialEq)]
struct TestIdTree {
    root_id: Option<IdTreeNodeId>,
    nodes: HashMap<IdTreeNodeId, IdTreeNode>,
}

impl IdTreeNodeLoader for TestIdTree {
    fn load_node(&self, id: IdTreeNodeId) -> Result<IdTreeNode> {
        match self.nodes.get(&id).cloned() {
            Some(n) => Ok(n),
            None => bail!("Cannot find node in TestIdTree"),
        }
    }
}

impl IdTreeNodeLoader for &'_ TestIdTree {
    fn load_node(&self, id: IdTreeNodeId) -> Result<IdTreeNode> {
        match self.nodes.get(&id).cloned() {
            Some(n) => Ok(n),
            None => bail!("Cannot find node in TestIdTree"),
        }
    }
}

impl TestIdTree {
    pub fn new() -> Self {
        Self {
            root_id: None,
            nodes: HashMap::new(),
        }
    }

    fn apply(&mut self, apply: Apply) {
        self.root_id = apply.root.id_tree_root_id;
        self.nodes.extend(apply.nodes.into_iter());
    }
}

fn get_dataset0() -> Vec<Object<i32>> {
    let mut res = Vec::new();

    let mut o1_keywords: HashSet<String> = HashSet::new();
    o1_keywords.insert("a".to_string());
    let o1: Object<i32> = Object::new(Height(1), vec![2], o1_keywords);
    let mut o2_keywords: HashSet<String> = HashSet::new();
    o2_keywords.insert("b".to_string());
    let o2: Object<i32> = Object::new(Height(1), vec![3], o2_keywords);
    let mut o3_keywords: HashSet<String> = HashSet::new();
    o3_keywords.insert("c".to_string());
    let o3: Object<i32> = Object::new(Height(1), vec![7], o3_keywords);

    res.push(o3);
    res.push(o2);
    res.push(o1);

    res
}

fn get_dataset1() -> Vec<Object<i32>> {
    let mut res = Vec::new();

    let mut o1_keywords: HashSet<String> = HashSet::new();
    o1_keywords.insert("a".to_string());
    let o1: Object<i32> = Object::new(Height(1), vec![2], o1_keywords);
    let mut o2_keywords: HashSet<String> = HashSet::new();
    o2_keywords.insert("b".to_string());
    let o2: Object<i32> = Object::new(Height(1), vec![3], o2_keywords);
    let mut o3_keywords: HashSet<String> = HashSet::new();
    o3_keywords.insert("c".to_string());
    let o3: Object<i32> = Object::new(Height(1), vec![7], o3_keywords);
    let mut o4_keywords: HashSet<String> = HashSet::new();
    o4_keywords.insert("d".to_string());
    let o4: Object<i32> = Object::new(Height(1), vec![4], o4_keywords);
    let mut o5_keywords: HashSet<String> = HashSet::new();
    o5_keywords.insert("e".to_string());
    let o5: Object<i32> = Object::new(Height(1), vec![2], o5_keywords);
    let mut o6_keywords: HashSet<String> = HashSet::new();
    o6_keywords.insert("f".to_string());
    let o6: Object<i32> = Object::new(Height(1), vec![4], o6_keywords);
    let mut o7_keywords: HashSet<String> = HashSet::new();
    o7_keywords.insert("g".to_string());
    let o7: Object<i32> = Object::new(Height(1), vec![10], o7_keywords);
    let mut o8_keywords: HashSet<String> = HashSet::new();
    o8_keywords.insert("h".to_string());
    let o8: Object<i32> = Object::new(Height(1), vec![9], o8_keywords);
    let mut o9_keywords: HashSet<String> = HashSet::new();
    o9_keywords.insert("i".to_string());
    let o9: Object<i32> = Object::new(Height(1), vec![8], o9_keywords);

    res.push(o9);
    res.push(o8);
    res.push(o7);
    res.push(o6);
    res.push(o5);
    res.push(o4);
    res.push(o3);
    res.push(o2);
    res.push(o1);

    res
}

pub const N: u16 = 3;
pub const K: u16 = 3;
pub const FANOUT: u8 = 3;

fn build_test_id_tree0() -> TestIdTree {
    let mut dataset = get_dataset0();
    let mut id_tree = TestIdTree::default();

    let obj1 = dataset.pop().unwrap();
    let leaf1 = create_id_tree_leaf(IdTreeNodeId(2), IdTreeInternalId(0), obj1.to_digest());
    let leaf1_id = leaf1.id;
    let leaf1_hash = leaf1.to_digest();
    id_tree.nodes.insert(leaf1_id, IdTreeNode::Leaf(leaf1));

    let obj2 = dataset.pop().unwrap();
    let leaf2 = create_id_tree_leaf(IdTreeNodeId(5), IdTreeInternalId(1), obj2.to_digest());
    let leaf2_id = leaf2.id;
    let leaf2_hash = leaf2.to_digest();
    id_tree.nodes.insert(leaf2_id, IdTreeNode::Leaf(leaf2));

    let obj3 = dataset.pop().unwrap();
    let leaf3 = create_id_tree_leaf(IdTreeNodeId(8), IdTreeInternalId(2), obj3.to_digest());
    let leaf3_id = leaf3.id;
    let leaf3_hash = leaf3.to_digest();
    id_tree.nodes.insert(leaf3_id, IdTreeNode::Leaf(leaf3));

    let mut non_leaf1_child_ids = SmallVec::new();
    non_leaf1_child_ids.push(leaf1_id);
    non_leaf1_child_ids.push(leaf2_id);
    non_leaf1_child_ids.push(leaf3_id);
    let mut non_leaf1_child_hashes = SmallVec::new();
    non_leaf1_child_hashes.push(leaf1_hash);
    non_leaf1_child_hashes.push(leaf2_hash);
    non_leaf1_child_hashes.push(leaf3_hash);
    let non_leaf1 =
        create_id_tree_non_leaf(IdTreeNodeId(7), non_leaf1_child_hashes, non_leaf1_child_ids);
    let non_leaf1_id = non_leaf1.id;
    id_tree
        .nodes
        .insert(non_leaf1_id, IdTreeNode::NonLeaf(Box::new(non_leaf1)));

    id_tree.root_id = Some(non_leaf1_id);
    id_tree
}

fn build_test_id_tree1() -> TestIdTree {
    let mut dataset = get_dataset1();
    let mut id_tree = TestIdTree::default();

    let obj1 = dataset.pop().unwrap();
    let leaf1 = create_id_tree_leaf(IdTreeNodeId(13), IdTreeInternalId(0), obj1.to_digest());
    let leaf1_id = leaf1.id;
    let leaf1_hash = leaf1.to_digest();
    id_tree.nodes.insert(leaf1_id, IdTreeNode::Leaf(leaf1));

    let obj2 = dataset.pop().unwrap();
    let leaf2 = create_id_tree_leaf(IdTreeNodeId(17), IdTreeInternalId(1), obj2.to_digest());
    let leaf2_id = leaf2.id;
    let leaf2_hash = leaf2.to_digest();
    id_tree.nodes.insert(leaf2_id, IdTreeNode::Leaf(leaf2));

    let obj3 = dataset.pop().unwrap();
    let leaf3 = create_id_tree_leaf(IdTreeNodeId(21), IdTreeInternalId(2), obj3.to_digest());
    let leaf3_id = leaf3.id;
    let leaf3_hash = leaf3.to_digest();
    id_tree.nodes.insert(leaf3_id, IdTreeNode::Leaf(leaf3));

    let mut non_leaf1_child_ids = SmallVec::new();
    non_leaf1_child_ids.push(leaf1_id);
    non_leaf1_child_ids.push(leaf2_id);
    non_leaf1_child_ids.push(leaf3_id);
    let mut non_leaf1_child_hashes = SmallVec::new();
    non_leaf1_child_hashes.push(leaf1_hash);
    non_leaf1_child_hashes.push(leaf2_hash);
    non_leaf1_child_hashes.push(leaf3_hash);
    let non_leaf1 = create_id_tree_non_leaf(
        IdTreeNodeId(20),
        non_leaf1_child_hashes,
        non_leaf1_child_ids,
    );
    let non_leaf1_id = non_leaf1.id;
    let non_leaf1_hash = non_leaf1.to_digest();
    id_tree
        .nodes
        .insert(non_leaf1_id, IdTreeNode::NonLeaf(Box::new(non_leaf1)));

    let obj4 = dataset.pop().unwrap();
    let leaf4 = create_id_tree_leaf(IdTreeNodeId(25), IdTreeInternalId(3), obj4.to_digest());
    let leaf4_id = leaf4.id;
    let leaf4_hash = leaf4.to_digest();
    id_tree.nodes.insert(leaf4_id, IdTreeNode::Leaf(leaf4));

    let obj5 = dataset.pop().unwrap();
    let leaf5 = create_id_tree_leaf(IdTreeNodeId(29), IdTreeInternalId(4), obj5.to_digest());
    let leaf5_id = leaf5.id;
    let leaf5_hash = leaf5.to_digest();
    id_tree.nodes.insert(leaf5_id, IdTreeNode::Leaf(leaf5));

    let obj6 = dataset.pop().unwrap();
    let leaf6 = create_id_tree_leaf(IdTreeNodeId(33), IdTreeInternalId(5), obj6.to_digest());
    let leaf6_id = leaf6.id;
    let leaf6_hash = leaf6.to_digest();
    id_tree.nodes.insert(leaf6_id, IdTreeNode::Leaf(leaf6));

    let mut non_leaf2_child_ids = SmallVec::new();
    non_leaf2_child_ids.push(leaf4_id);
    non_leaf2_child_ids.push(leaf5_id);
    non_leaf2_child_ids.push(leaf6_id);
    let mut non_leaf2_child_hashes = SmallVec::new();
    non_leaf2_child_hashes.push(leaf4_hash);
    non_leaf2_child_hashes.push(leaf5_hash);
    non_leaf2_child_hashes.push(leaf6_hash);
    let non_leaf2 = create_id_tree_non_leaf(
        IdTreeNodeId(32),
        non_leaf2_child_hashes,
        non_leaf2_child_ids,
    );
    let non_leaf2_id = non_leaf2.id;
    let non_leaf2_hash = non_leaf2.to_digest();
    id_tree
        .nodes
        .insert(non_leaf2_id, IdTreeNode::NonLeaf(Box::new(non_leaf2)));

    let obj7 = dataset.pop().unwrap();
    let leaf7 = create_id_tree_leaf(IdTreeNodeId(37), IdTreeInternalId(6), obj7.to_digest());
    let leaf7_id = leaf7.id;
    let leaf7_hash = leaf7.to_digest();
    id_tree.nodes.insert(leaf7_id, IdTreeNode::Leaf(leaf7));

    let obj8 = dataset.pop().unwrap();
    let leaf8 = create_id_tree_leaf(IdTreeNodeId(41), IdTreeInternalId(7), obj8.to_digest());
    let leaf8_id = leaf8.id;
    let leaf8_hash = leaf8.to_digest();
    id_tree.nodes.insert(leaf8_id, IdTreeNode::Leaf(leaf8));

    let obj9 = dataset.pop().unwrap();
    let leaf9 = create_id_tree_leaf(IdTreeNodeId(45), IdTreeInternalId(8), obj9.to_digest());
    let leaf9_id = leaf9.id;
    let leaf9_hash = leaf9.to_digest();
    id_tree.nodes.insert(leaf9_id, IdTreeNode::Leaf(leaf9));

    let mut non_leaf3_child_ids = SmallVec::new();
    non_leaf3_child_ids.push(leaf7_id);
    non_leaf3_child_ids.push(leaf8_id);
    non_leaf3_child_ids.push(leaf9_id);
    let mut non_leaf3_child_hashes = SmallVec::new();
    non_leaf3_child_hashes.push(leaf7_hash);
    non_leaf3_child_hashes.push(leaf8_hash);
    non_leaf3_child_hashes.push(leaf9_hash);
    let non_leaf3 = create_id_tree_non_leaf(
        IdTreeNodeId(44),
        non_leaf3_child_hashes,
        non_leaf3_child_ids,
    );
    let non_leaf3_id = non_leaf3.id;
    let non_leaf3_hash = non_leaf3.to_digest();
    id_tree
        .nodes
        .insert(non_leaf3_id, IdTreeNode::NonLeaf(Box::new(non_leaf3)));

    let mut non_leaf4_child_ids = SmallVec::new();
    non_leaf4_child_ids.push(non_leaf1_id);
    non_leaf4_child_ids.push(non_leaf2_id);
    non_leaf4_child_ids.push(non_leaf3_id);
    let mut non_leaf4_child_hashes = SmallVec::new();
    non_leaf4_child_hashes.push(non_leaf1_hash);
    non_leaf4_child_hashes.push(non_leaf2_hash);
    non_leaf4_child_hashes.push(non_leaf3_hash);
    let non_leaf4 = create_id_tree_non_leaf(
        IdTreeNodeId(43),
        non_leaf4_child_hashes,
        non_leaf4_child_ids,
    );
    let non_leaf4_id = non_leaf4.id;
    id_tree
        .nodes
        .insert(non_leaf4_id, IdTreeNode::NonLeaf(Box::new(non_leaf4)));

    id_tree.root_id = Some(non_leaf4_id);
    id_tree
}

fn set_id_root_id(id_tree_root: &mut IdTreeRoot, id: Option<IdTreeNodeId>) {
    id_tree_root.id_tree_root_id = id;
}

#[test]
fn test_write0() {
    let n = 1;
    let k = 3;
    let mut dataset = get_dataset0();
    let mut id_tree = TestIdTree::new();
    let mut id_tree_root = IdTreeRoot::default();
    set_id_root_id(&mut id_tree_root, id_tree.root_id);
    let mut ctx = WriteContext::new(&id_tree, id_tree_root);

    for _i in 0..3 {
        let obj = dataset.pop().unwrap();
        let obj_hash = obj.to_digest();
        ctx.insert(obj_hash, n * k, FANOUT).unwrap();
    }
    let changes = ctx.changes();
    id_tree.apply(changes);
    assert_eq!(build_test_id_tree0(), id_tree);
}

#[test]
fn test_write1() {
    let mut dataset = get_dataset1();
    let mut id_tree = TestIdTree::new();
    let mut id_tree_root = IdTreeRoot::default();
    set_id_root_id(&mut id_tree_root, id_tree.root_id);
    let mut ctx = WriteContext::new(&id_tree, id_tree_root);

    for _i in 0..9 {
        let obj = dataset.pop().unwrap();
        let obj_hash = obj.to_digest();
        ctx.insert(obj_hash, N * K, FANOUT).unwrap();
    }
    let changes = ctx.changes();
    id_tree.apply(changes);
    assert_eq!(build_test_id_tree1(), id_tree);
}

#[test]
fn test_read1() {
    let id_tree = build_test_id_tree1();

    let v = query_without_proof(
        N * K,
        &id_tree,
        id_tree.root_id.unwrap(),
        IdTreeInternalId(11),
        FANOUT,
    )
    .unwrap();
    assert_eq!(None, v);
    let (v, p) = query_id_tree(
        N * K,
        &id_tree,
        id_tree.root_id,
        IdTreeInternalId(11),
        FANOUT,
    )
    .unwrap();
    assert_eq!(None, v);
    unsafe {
        p.verify_value(
            Digest::zero(),
            ObjId(NonZeroU16::new_unchecked(12)),
            N * K,
            FANOUT,
        )
        .unwrap();
    }
    assert_eq!(
        id_tree
            .load_node(id_tree.root_id.unwrap())
            .unwrap()
            .to_digest(),
        p.root_hash()
    );

    let v = query_without_proof(
        N * K,
        &id_tree,
        id_tree.root_id.unwrap(),
        IdTreeInternalId(0),
        FANOUT,
    )
    .unwrap();
    let mut o1_keywords: HashSet<String> = HashSet::new();
    o1_keywords.insert("a".to_string());
    let o1: Object<i32> = Object::new(Height(1), vec![2], o1_keywords);
    let o1_digest = o1.to_digest();
    assert_eq!(Some(o1_digest), v);
    let (v, p) = query_id_tree(
        N * K,
        &id_tree,
        id_tree.root_id,
        IdTreeInternalId(0),
        FANOUT,
    )
    .unwrap();
    assert_eq!(Some(o1_digest), v);
    assert_eq!(
        id_tree
            .load_node(id_tree.root_id.unwrap())
            .unwrap()
            .to_digest(),
        p.root_hash()
    );
    let mut state = blake2().to_state();
    state.update(&IdTreeInternalId(0).to_le_bytes());
    state.update(o1_digest.as_bytes());
    let n_digest = Digest::from(state.finalize());
    unsafe {
        p.verify_value(n_digest, ObjId(NonZeroU16::new_unchecked(1)), N * K, FANOUT)
            .unwrap();
    }

    let v = query_without_proof(
        N * K,
        &id_tree,
        id_tree.root_id.unwrap(),
        IdTreeInternalId(1),
        FANOUT,
    )
    .unwrap();
    let mut o2_keywords: HashSet<String> = HashSet::new();
    o2_keywords.insert("b".to_string());
    let o2: Object<i32> = Object::new(Height(1), vec![3], o2_keywords);
    let o2_digest = o2.to_digest();
    assert_eq!(Some(o2_digest), v);
    let (v, p) = query_id_tree(
        N * K,
        &id_tree,
        id_tree.root_id,
        IdTreeInternalId(1),
        FANOUT,
    )
    .unwrap();
    assert_eq!(Some(o2_digest), v);
    assert_eq!(
        id_tree
            .load_node(id_tree.root_id.unwrap())
            .unwrap()
            .to_digest(),
        p.root_hash()
    );
    let mut state = blake2().to_state();
    state.update(&IdTreeInternalId(1).to_le_bytes());
    state.update(o2_digest.as_bytes());
    let n_digest = Digest::from(state.finalize());
    unsafe {
        p.verify_value(n_digest, ObjId(NonZeroU16::new_unchecked(2)), N * K, FANOUT)
            .unwrap();
    }

    let v = query_without_proof(
        N * K,
        &id_tree,
        id_tree.root_id.unwrap(),
        IdTreeInternalId(2),
        FANOUT,
    )
    .unwrap();
    let mut o3_keywords: HashSet<String> = HashSet::new();
    o3_keywords.insert("c".to_string());
    let o3: Object<i32> = Object::new(Height(1), vec![7], o3_keywords);
    let o3_digest = o3.to_digest();
    assert_eq!(Some(o3_digest), v);
    let (v, p) = query_id_tree(
        N * K,
        &id_tree,
        id_tree.root_id,
        IdTreeInternalId(2),
        FANOUT,
    )
    .unwrap();
    assert_eq!(Some(o3_digest), v);
    assert_eq!(
        id_tree
            .load_node(id_tree.root_id.unwrap())
            .unwrap()
            .to_digest(),
        p.root_hash()
    );
    let mut state = blake2().to_state();
    state.update(&IdTreeInternalId(2).to_le_bytes());
    state.update(o3_digest.as_bytes());
    let n_digest = Digest::from(state.finalize());
    unsafe {
        p.verify_value(n_digest, ObjId(NonZeroU16::new_unchecked(3)), N * K, FANOUT)
            .unwrap();
    }
}

#[test]
fn test_read_ctx1() {
    let id_tree = build_test_id_tree1();
    let mut ctx1 = ReadContext::new(&id_tree, id_tree.root_id);

    let mut o1_keywords: HashSet<String> = HashSet::new();
    o1_keywords.insert("a".to_string());
    let o1: Object<i32> = Object::new(Height(1), vec![2], o1_keywords);
    let o1_digest = o1.to_digest();
    let mut o2_keywords: HashSet<String> = HashSet::new();
    o2_keywords.insert("b".to_string());
    let o2: Object<i32> = Object::new(Height(1), vec![3], o2_keywords);
    let o2_digest = o2.to_digest();
    let mut o3_keywords: HashSet<String> = HashSet::new();
    o3_keywords.insert("c".to_string());
    let o3: Object<i32> = Object::new(Height(1), vec![7], o3_keywords);
    let o3_digest = o3.to_digest();
    let mut o4_keywords: HashSet<String> = HashSet::new();
    o4_keywords.insert("d".to_string());
    let o4: Object<i32> = Object::new(Height(1), vec![4], o4_keywords);
    let o4_digest = o4.to_digest();
    let mut o5_keywords: HashSet<String> = HashSet::new();
    o5_keywords.insert("e".to_string());
    let o5: Object<i32> = Object::new(Height(1), vec![2], o5_keywords);
    let o5_digest = o5.to_digest();
    let mut o6_keywords: HashSet<String> = HashSet::new();
    o6_keywords.insert("f".to_string());
    let o6: Object<i32> = Object::new(Height(1), vec![4], o6_keywords);
    let o6_digest = o6.to_digest();
    let mut o7_keywords: HashSet<String> = HashSet::new();
    o7_keywords.insert("g".to_string());
    let o7: Object<i32> = Object::new(Height(1), vec![10], o7_keywords);
    let o7_digest = o7.to_digest();
    let mut o8_keywords: HashSet<String> = HashSet::new();
    o8_keywords.insert("h".to_string());
    let o8: Object<i32> = Object::new(Height(1), vec![9], o8_keywords);
    let o8_digest = o8.to_digest();
    let mut o9_keywords: HashSet<String> = HashSet::new();
    o9_keywords.insert("i".to_string());
    let o9: Object<i32> = Object::new(Height(1), vec![8], o9_keywords);
    let o9_digest = o9.to_digest();
    unsafe {
        let v = ctx1
            .query(ObjId(NonZeroU16::new_unchecked(11)), N * K, FANOUT)
            .unwrap();
        assert_eq!(None, v);
        let v = ctx1
            .query(ObjId(NonZeroU16::new_unchecked(1)), N * K, FANOUT)
            .unwrap();
        assert_eq!(Some(o1_digest), v);
        let v = ctx1
            .query(ObjId(NonZeroU16::new_unchecked(2)), N * K, FANOUT)
            .unwrap();
        assert_eq!(Some(o2_digest), v);
        let v = ctx1
            .query(ObjId(NonZeroU16::new_unchecked(3)), N * K, FANOUT)
            .unwrap();
        assert_eq!(Some(o3_digest), v);
        let v = ctx1
            .query(ObjId(NonZeroU16::new_unchecked(4)), N * K, FANOUT)
            .unwrap();
        assert_eq!(Some(o4_digest), v);
        let v = ctx1
            .query(ObjId(NonZeroU16::new_unchecked(5)), N * K, FANOUT)
            .unwrap();
        assert_eq!(Some(o5_digest), v);
        let v = ctx1
            .query(ObjId(NonZeroU16::new_unchecked(6)), N * K, FANOUT)
            .unwrap();
        assert_eq!(Some(o6_digest), v);
        let v = ctx1
            .query(ObjId(NonZeroU16::new_unchecked(7)), N * K, FANOUT)
            .unwrap();
        assert_eq!(Some(o7_digest), v);
        let v = ctx1
            .query(ObjId(NonZeroU16::new_unchecked(8)), N * K, FANOUT)
            .unwrap();
        assert_eq!(Some(o8_digest), v);
        let v = ctx1
            .query(ObjId(NonZeroU16::new_unchecked(9)), N * K, FANOUT)
            .unwrap();
        assert_eq!(Some(o9_digest), v);
    }
    let p = ctx1.into_proof();

    assert_eq!(
        id_tree
            .load_node(id_tree.root_id.unwrap())
            .unwrap()
            .to_digest(),
        p.root_hash()
    );
    unsafe {
        p.verify_value(
            Digest::zero(),
            ObjId(NonZeroU16::new_unchecked(12)),
            N * K,
            FANOUT,
        )
        .unwrap();
    }

    let mut state = blake2().to_state();
    state.update(&IdTreeInternalId(0).to_le_bytes());
    state.update(o1_digest.as_bytes());
    let n1_digest = Digest::from(state.finalize());
    unsafe {
        p.verify_value(
            n1_digest,
            ObjId(NonZeroU16::new_unchecked(1)),
            N * K,
            FANOUT,
        )
        .unwrap();
    }
    let mut state = blake2().to_state();
    state.update(&IdTreeInternalId(1).to_le_bytes());
    state.update(o2_digest.as_bytes());
    let n2_digest = Digest::from(state.finalize());
    unsafe {
        p.verify_value(
            n2_digest,
            ObjId(NonZeroU16::new_unchecked(2)),
            N * K,
            FANOUT,
        )
        .unwrap();
    }
    let mut state = blake2().to_state();
    state.update(&IdTreeInternalId(2).to_le_bytes());
    state.update(o3_digest.as_bytes());
    let n3_digest = Digest::from(state.finalize());
    unsafe {
        p.verify_value(
            n3_digest,
            ObjId(NonZeroU16::new_unchecked(3)),
            N * K,
            FANOUT,
        )
        .unwrap();
    }
    let mut state = blake2().to_state();
    state.update(&IdTreeInternalId(3).to_le_bytes());
    state.update(o4_digest.as_bytes());
    let n4_digest = Digest::from(state.finalize());
    unsafe {
        p.verify_value(
            n4_digest,
            ObjId(NonZeroU16::new_unchecked(4)),
            N * K,
            FANOUT,
        )
        .unwrap();
    }
    let mut state = blake2().to_state();
    state.update(&IdTreeInternalId(4).to_le_bytes());
    state.update(o5_digest.as_bytes());
    let n5_digest = Digest::from(state.finalize());
    unsafe {
        p.verify_value(
            n5_digest,
            ObjId(NonZeroU16::new_unchecked(5)),
            N * K,
            FANOUT,
        )
        .unwrap();
    }
    let mut state = blake2().to_state();
    state.update(&IdTreeInternalId(5).to_le_bytes());
    state.update(o6_digest.as_bytes());
    let n6_digest = Digest::from(state.finalize());
    unsafe {
        p.verify_value(
            n6_digest,
            ObjId(NonZeroU16::new_unchecked(6)),
            N * K,
            FANOUT,
        )
        .unwrap();
    }
    let mut state = blake2().to_state();
    state.update(&IdTreeInternalId(6).to_le_bytes());
    state.update(o7_digest.as_bytes());
    let n7_digest = Digest::from(state.finalize());
    unsafe {
        p.verify_value(
            n7_digest,
            ObjId(NonZeroU16::new_unchecked(7)),
            N * K,
            FANOUT,
        )
        .unwrap();
    }
    let mut state = blake2().to_state();
    state.update(&IdTreeInternalId(7).to_le_bytes());
    state.update(o8_digest.as_bytes());
    let n8_digest = Digest::from(state.finalize());
    unsafe {
        p.verify_value(
            n8_digest,
            ObjId(NonZeroU16::new_unchecked(8)),
            N * K,
            FANOUT,
        )
        .unwrap();
    }
    let mut state = blake2().to_state();
    state.update(&IdTreeInternalId(8).to_le_bytes());
    state.update(o9_digest.as_bytes());
    let n9_digest = Digest::from(state.finalize());
    unsafe {
        p.verify_value(
            n9_digest,
            ObjId(NonZeroU16::new_unchecked(9)),
            N * K,
            FANOUT,
        )
        .unwrap();
    }
}

use serde::{Deserialize, Serialize};
#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
struct TestLeaf {
    node_id: Option<IdTreeNodeId>,
    node_hash: Digest,
}

#[test]
fn test_proof_size() {
    let leaf1 = TestLeaf {
        node_id: Some(IdTreeNodeId(1)),
        node_hash: Digest::zero(),
    };
    let leaf2 = TestLeaf {
        node_id: None,
        node_hash: Digest::zero(),
    };
    let leaf1_size = bincode::serialize(&leaf1).unwrap().len();
    let leaf2_size = bincode::serialize(&leaf2).unwrap().len();

    assert_eq!(4, leaf1_size - leaf2_size);
}
