#![allow(unused)]
use super::{
    read::{query_id_tree, query_without_proof, ReadContext},
    write::{Apply, WriteContext},
    IdTreeLeafNode, IdTreeNode, IdTreeNodeId, IdTreeNodeLoader, IdTreeNonLeafNode, IdTreeObjId,
};
use crate::{
    chain::{
        block::BlockId,
        object::{ObjId, Object},
        IDTREE_FANOUT,
    },
    digest::{blake2, Digest, Digestible},
};
use anyhow::Result;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Default, Clone, Eq, PartialEq)]
struct TestIdTree {
    root_id: IdTreeNodeId,
    nodes: HashMap<IdTreeNodeId, IdTreeNode>,
}

impl IdTreeNodeLoader for TestIdTree {
    fn load_node(&self, id: IdTreeNodeId) -> Result<Option<IdTreeNode>> {
        match self.nodes.get(&id).cloned() {
            Some(n) => Ok(Some(n)),
            None => Ok(None),
        }
    }
}

impl IdTreeNodeLoader for &'_ TestIdTree {
    fn load_node(&self, id: IdTreeNodeId) -> Result<Option<IdTreeNode>> {
        match self.nodes.get(&id).cloned() {
            Some(n) => Ok(Some(n)),
            None => Ok(None),
        }
    }
}

impl TestIdTree {
    pub fn new() -> Self {
        Self {
            root_id: IdTreeNodeId::next_id(),
            nodes: HashMap::new(),
        }
    }

    fn apply(&mut self, apply: Apply) {
        self.root_id = apply.root_id;
        self.nodes.extend(apply.nodes.into_iter());
    }
}

fn get_dataset0() -> Vec<Object<i32>> {
    let mut res = Vec::new();

    let mut o1_keywords: HashSet<String> = HashSet::new();
    o1_keywords.insert("a".to_string());
    let o1: Object<i32> = Object::new_dbg(ObjId(0), BlockId(1), vec![2], o1_keywords);
    let mut o2_keywords: HashSet<String> = HashSet::new();
    o2_keywords.insert("b".to_string());
    let o2: Object<i32> = Object::new_dbg(ObjId(1), BlockId(1), vec![3], o2_keywords);
    let mut o3_keywords: HashSet<String> = HashSet::new();
    o3_keywords.insert("c".to_string());
    let o3: Object<i32> = Object::new_dbg(ObjId(2), BlockId(1), vec![7], o3_keywords);

    res.push(o3);
    res.push(o2);
    res.push(o1);

    res
}

fn get_dataset1() -> Vec<Object<i32>> {
    let mut res = Vec::new();

    let mut o1_keywords: HashSet<String> = HashSet::new();
    o1_keywords.insert("a".to_string());
    let o1: Object<i32> = Object::new_dbg(ObjId(0), BlockId(1), vec![2], o1_keywords);
    let mut o2_keywords: HashSet<String> = HashSet::new();
    o2_keywords.insert("b".to_string());
    let o2: Object<i32> = Object::new_dbg(ObjId(1), BlockId(1), vec![3], o2_keywords);
    let mut o3_keywords: HashSet<String> = HashSet::new();
    o3_keywords.insert("c".to_string());
    let o3: Object<i32> = Object::new_dbg(ObjId(2), BlockId(1), vec![7], o3_keywords);
    let mut o4_keywords: HashSet<String> = HashSet::new();
    o4_keywords.insert("d".to_string());
    let o4: Object<i32> = Object::new_dbg(ObjId(3), BlockId(1), vec![4], o4_keywords);
    let mut o5_keywords: HashSet<String> = HashSet::new();
    o5_keywords.insert("e".to_string());
    let o5: Object<i32> = Object::new_dbg(ObjId(4), BlockId(1), vec![2], o5_keywords);
    let mut o6_keywords: HashSet<String> = HashSet::new();
    o6_keywords.insert("f".to_string());
    let o6: Object<i32> = Object::new_dbg(ObjId(5), BlockId(1), vec![4], o6_keywords);
    let mut o7_keywords: HashSet<String> = HashSet::new();
    o7_keywords.insert("g".to_string());
    let o7: Object<i32> = Object::new_dbg(ObjId(6), BlockId(1), vec![10], o7_keywords);
    let mut o8_keywords: HashSet<String> = HashSet::new();
    o8_keywords.insert("h".to_string());
    let o8: Object<i32> = Object::new_dbg(ObjId(7), BlockId(1), vec![9], o8_keywords);
    let mut o9_keywords: HashSet<String> = HashSet::new();
    o9_keywords.insert("i".to_string());
    let o9: Object<i32> = Object::new_dbg(ObjId(8), BlockId(1), vec![8], o9_keywords);

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

pub const N: usize = 3;
pub const K: usize = 3;

fn build_test_id_tree0() -> TestIdTree {
    let mut dataset = get_dataset0();
    let mut id_tree = TestIdTree::default();

    let obj1 = dataset.pop().unwrap();
    let leaf1 = IdTreeLeafNode::new_dbg(
        IdTreeNodeId(2),
        IdTreeObjId(obj1.id.unwrap() % (N * K) as u64),
        obj1.to_digest(),
    );
    let leaf1_id = leaf1.id;
    let leaf1_hash = leaf1.to_digest();
    id_tree.nodes.insert(leaf1_id, IdTreeNode::Leaf(leaf1));

    let obj2 = dataset.pop().unwrap();
    let leaf2 = IdTreeLeafNode::new_dbg(
        IdTreeNodeId(5),
        IdTreeObjId(obj2.id.unwrap() % (N * K) as u64),
        obj2.to_digest(),
    );
    let leaf2_id = leaf2.id;
    let leaf2_hash = leaf2.to_digest();
    id_tree.nodes.insert(leaf2_id, IdTreeNode::Leaf(leaf2));

    let obj3 = dataset.pop().unwrap();
    let leaf3 = IdTreeLeafNode::new_dbg(
        IdTreeNodeId(8),
        IdTreeObjId(obj3.id.unwrap() % (N * K) as u64),
        obj3.to_digest(),
    );
    let leaf3_id = leaf3.id;
    let leaf3_hash = leaf3.to_digest();
    id_tree.nodes.insert(leaf3_id, IdTreeNode::Leaf(leaf3));

    let mut non_leaf1_child_ids = [IdTreeNodeId(0); IDTREE_FANOUT];
    non_leaf1_child_ids[0] = leaf1_id;
    non_leaf1_child_ids[1] = leaf2_id;
    non_leaf1_child_ids[2] = leaf3_id;
    let mut non_leaf1_child_hashes = [Digest::zero(); IDTREE_FANOUT];
    non_leaf1_child_hashes[0] = leaf1_hash;
    non_leaf1_child_hashes[1] = leaf2_hash;
    non_leaf1_child_hashes[2] = leaf3_hash;
    let non_leaf1 =
        IdTreeNonLeafNode::new_dbg(IdTreeNodeId(7), non_leaf1_child_hashes, non_leaf1_child_ids);
    let non_leaf1_id = non_leaf1.id;
    id_tree
        .nodes
        .insert(non_leaf1_id, IdTreeNode::NonLeaf(non_leaf1));

    id_tree.root_id = non_leaf1_id;
    id_tree
}

fn build_test_id_tree1() -> TestIdTree {
    let mut dataset = get_dataset1();
    let mut id_tree = TestIdTree::default();

    let obj1 = dataset.pop().unwrap();
    let leaf1 = IdTreeLeafNode::new_dbg(
        IdTreeNodeId(13),
        IdTreeObjId(obj1.id.unwrap() % (N * K) as u64),
        obj1.to_digest(),
    );
    let leaf1_id = leaf1.id;
    let leaf1_hash = leaf1.to_digest();
    id_tree.nodes.insert(leaf1_id, IdTreeNode::Leaf(leaf1));

    let obj2 = dataset.pop().unwrap();
    let leaf2 = IdTreeLeafNode::new_dbg(
        IdTreeNodeId(17),
        IdTreeObjId(obj2.id.unwrap() % (N * K) as u64),
        obj2.to_digest(),
    );
    let leaf2_id = leaf2.id;
    let leaf2_hash = leaf2.to_digest();
    id_tree.nodes.insert(leaf2_id, IdTreeNode::Leaf(leaf2));

    let obj3 = dataset.pop().unwrap();
    let leaf3 = IdTreeLeafNode::new_dbg(
        IdTreeNodeId(21),
        IdTreeObjId(obj3.id.unwrap() % (N * K) as u64),
        obj3.to_digest(),
    );
    let leaf3_id = leaf3.id;
    let leaf3_hash = leaf3.to_digest();
    id_tree.nodes.insert(leaf3_id, IdTreeNode::Leaf(leaf3));

    let mut non_leaf1_child_ids = [IdTreeNodeId(0); IDTREE_FANOUT];
    non_leaf1_child_ids[0] = leaf1_id;
    non_leaf1_child_ids[1] = leaf2_id;
    non_leaf1_child_ids[2] = leaf3_id;
    let mut non_leaf1_child_hashes = [Digest::zero(); IDTREE_FANOUT];
    non_leaf1_child_hashes[0] = leaf1_hash;
    non_leaf1_child_hashes[1] = leaf2_hash;
    non_leaf1_child_hashes[2] = leaf3_hash;
    let non_leaf1 = IdTreeNonLeafNode::new_dbg(
        IdTreeNodeId(20),
        non_leaf1_child_hashes,
        non_leaf1_child_ids,
    );
    let non_leaf1_id = non_leaf1.id;
    let non_leaf1_hash = non_leaf1.to_digest();
    id_tree
        .nodes
        .insert(non_leaf1_id, IdTreeNode::NonLeaf(non_leaf1));

    let obj4 = dataset.pop().unwrap();
    let leaf4 = IdTreeLeafNode::new_dbg(
        IdTreeNodeId(25),
        IdTreeObjId(obj4.id.unwrap() % (N * K) as u64),
        obj4.to_digest(),
    );
    let leaf4_id = leaf4.id;
    let leaf4_hash = leaf4.to_digest();
    id_tree.nodes.insert(leaf4_id, IdTreeNode::Leaf(leaf4));

    let obj5 = dataset.pop().unwrap();
    let leaf5 = IdTreeLeafNode::new_dbg(
        IdTreeNodeId(29),
        IdTreeObjId(obj5.id.unwrap() % (N * K) as u64),
        obj5.to_digest(),
    );
    let leaf5_id = leaf5.id;
    let leaf5_hash = leaf5.to_digest();
    id_tree.nodes.insert(leaf5_id, IdTreeNode::Leaf(leaf5));

    let obj6 = dataset.pop().unwrap();
    let leaf6 = IdTreeLeafNode::new_dbg(
        IdTreeNodeId(33),
        IdTreeObjId(obj6.id.unwrap() % (N * K) as u64),
        obj6.to_digest(),
    );
    let leaf6_id = leaf6.id;
    let leaf6_hash = leaf6.to_digest();
    id_tree.nodes.insert(leaf6_id, IdTreeNode::Leaf(leaf6));

    let mut non_leaf2_child_ids = [IdTreeNodeId(0); IDTREE_FANOUT];
    non_leaf2_child_ids[0] = leaf4_id;
    non_leaf2_child_ids[1] = leaf5_id;
    non_leaf2_child_ids[2] = leaf6_id;
    let mut non_leaf2_child_hashes = [Digest::zero(); IDTREE_FANOUT];
    non_leaf2_child_hashes[0] = leaf4_hash;
    non_leaf2_child_hashes[1] = leaf5_hash;
    non_leaf2_child_hashes[2] = leaf6_hash;
    let non_leaf2 = IdTreeNonLeafNode::new_dbg(
        IdTreeNodeId(32),
        non_leaf2_child_hashes,
        non_leaf2_child_ids,
    );
    let non_leaf2_id = non_leaf2.id;
    let non_leaf2_hash = non_leaf2.to_digest();
    id_tree
        .nodes
        .insert(non_leaf2_id, IdTreeNode::NonLeaf(non_leaf2));

    let obj7 = dataset.pop().unwrap();
    let leaf7 = IdTreeLeafNode::new_dbg(
        IdTreeNodeId(37),
        IdTreeObjId(obj7.id.unwrap() % (N * K) as u64),
        obj7.to_digest(),
    );
    let leaf7_id = leaf7.id;
    let leaf7_hash = leaf7.to_digest();
    id_tree.nodes.insert(leaf7_id, IdTreeNode::Leaf(leaf7));

    let obj8 = dataset.pop().unwrap();
    let leaf8 = IdTreeLeafNode::new_dbg(
        IdTreeNodeId(41),
        IdTreeObjId(obj8.id.unwrap() % (N * K) as u64),
        obj8.to_digest(),
    );
    let leaf8_id = leaf8.id;
    let leaf8_hash = leaf8.to_digest();
    id_tree.nodes.insert(leaf8_id, IdTreeNode::Leaf(leaf8));

    let obj9 = dataset.pop().unwrap();
    let leaf9 = IdTreeLeafNode::new_dbg(
        IdTreeNodeId(45),
        IdTreeObjId(obj9.id.unwrap() % (N * K) as u64),
        obj9.to_digest(),
    );
    let leaf9_id = leaf9.id;
    let leaf9_hash = leaf9.to_digest();
    id_tree.nodes.insert(leaf9_id, IdTreeNode::Leaf(leaf9));

    let mut non_leaf3_child_ids = [IdTreeNodeId(0); IDTREE_FANOUT];
    non_leaf3_child_ids[0] = leaf7_id;
    non_leaf3_child_ids[1] = leaf8_id;
    non_leaf3_child_ids[2] = leaf9_id;
    let mut non_leaf3_child_hashes = [Digest::zero(); IDTREE_FANOUT];
    non_leaf3_child_hashes[0] = leaf7_hash;
    non_leaf3_child_hashes[1] = leaf8_hash;
    non_leaf3_child_hashes[2] = leaf9_hash;
    let non_leaf3 = IdTreeNonLeafNode::new_dbg(
        IdTreeNodeId(44),
        non_leaf3_child_hashes,
        non_leaf3_child_ids,
    );
    let non_leaf3_id = non_leaf3.id;
    let non_leaf3_hash = non_leaf3.to_digest();
    id_tree
        .nodes
        .insert(non_leaf3_id, IdTreeNode::NonLeaf(non_leaf3));

    let mut non_leaf4_child_ids = [IdTreeNodeId(0); IDTREE_FANOUT];
    non_leaf4_child_ids[0] = non_leaf1_id;
    non_leaf4_child_ids[1] = non_leaf2_id;
    non_leaf4_child_ids[2] = non_leaf3_id;
    let mut non_leaf4_child_hashes = [Digest::zero(); IDTREE_FANOUT];
    non_leaf4_child_hashes[0] = non_leaf1_hash;
    non_leaf4_child_hashes[1] = non_leaf2_hash;
    non_leaf4_child_hashes[2] = non_leaf3_hash;
    let non_leaf4 = IdTreeNonLeafNode::new_dbg(
        IdTreeNodeId(43),
        non_leaf4_child_hashes,
        non_leaf4_child_ids,
    );
    let non_leaf4_id = non_leaf4.id;
    id_tree
        .nodes
        .insert(non_leaf4_id, IdTreeNode::NonLeaf(non_leaf4));

    id_tree.root_id = non_leaf4_id;
    id_tree
}

#[test]
fn test_write0() {
    let n = 1;
    let k = 3;
    let mut dataset = get_dataset0();
    let mut id_tree = TestIdTree::new();
    println!("{:?}", id_tree);
    let mut ctx = WriteContext::new(&id_tree, id_tree.root_id);

    for _i in 0..3 {
        let obj = dataset.pop().unwrap();
        let obj_id = IdTreeObjId(obj.id.unwrap() % (n * k) as u64);
        let obj_hash = obj.to_digest();
        let _res = ctx.insert(obj_id, obj_hash, n * k);
    }
    let changes = ctx.changes();
    id_tree.apply(changes);
    assert_eq!(build_test_id_tree0(), id_tree);
    dbg!(id_tree);
}

#[test]
fn test_write1() {
    let mut dataset = get_dataset1();
    let mut id_tree = TestIdTree::new();
    println!("{:?}", id_tree);
    let mut ctx = WriteContext::new(&id_tree, id_tree.root_id);

    for _i in 0..9 {
        let obj = dataset.pop().unwrap();
        let obj_id = IdTreeObjId(obj.id.unwrap() % (N * K) as u64);
        let obj_hash = obj.to_digest();
        let _res = ctx.insert(obj_id, obj_hash, N * K);
    }
    let changes = ctx.changes();
    id_tree.apply(changes);
    assert_eq!(build_test_id_tree1(), id_tree);
    dbg!(id_tree);
}

#[test]
fn test_read1() {
    let id_tree = build_test_id_tree1();

    let v = query_without_proof(N * K, &id_tree, id_tree.root_id, IdTreeObjId(11)).unwrap();
    assert_eq!(None, v);
    let (v, p) = query_id_tree(N * K, &id_tree, id_tree.root_id, IdTreeObjId(11)).unwrap();
    assert_eq!(None, v);
    assert!(p.value_hash(IdTreeObjId(11), N * K).unwrap().is_zero());
    assert_eq!(
        id_tree
            .load_node(id_tree.root_id)
            .unwrap()
            .unwrap()
            .to_digest(),
        p.root_hash()
    );

    let v = query_without_proof(N * K, &id_tree, id_tree.root_id, IdTreeObjId(0)).unwrap();
    let mut o1_keywords: HashSet<String> = HashSet::new();
    o1_keywords.insert("a".to_string());
    let o1: Object<i32> = Object::new_dbg(ObjId(0), BlockId(1), vec![2], o1_keywords);
    let o1_digest = o1.to_digest();
    assert_eq!(Some(o1_digest), v);
    let (v, p) = query_id_tree(N * K, &id_tree, id_tree.root_id, IdTreeObjId(0)).unwrap();
    assert_eq!(Some(o1_digest), v);
    assert_eq!(
        id_tree
            .load_node(id_tree.root_id)
            .unwrap()
            .unwrap()
            .to_digest(),
        p.root_hash()
    );
    let mut state = blake2().to_state();
    state.update(&IdTreeObjId(0).to_le_bytes());
    state.update(o1_digest.as_bytes());
    let n_digest = Digest::from(state.finalize());
    assert_eq!(Some(n_digest), p.value_hash(IdTreeObjId(0), N * K));

    let v = query_without_proof(N * K, &id_tree, id_tree.root_id, IdTreeObjId(1)).unwrap();
    let mut o2_keywords: HashSet<String> = HashSet::new();
    o2_keywords.insert("b".to_string());
    let o2: Object<i32> = Object::new_dbg(ObjId(1), BlockId(1), vec![3], o2_keywords);
    let o2_digest = o2.to_digest();
    assert_eq!(Some(o2_digest), v);
    let (v, p) = query_id_tree(N * K, &id_tree, id_tree.root_id, IdTreeObjId(1)).unwrap();
    assert_eq!(Some(o2_digest), v);
    assert_eq!(
        id_tree
            .load_node(id_tree.root_id)
            .unwrap()
            .unwrap()
            .to_digest(),
        p.root_hash()
    );
    let mut state = blake2().to_state();
    state.update(&IdTreeObjId(1).to_le_bytes());
    state.update(o2_digest.as_bytes());
    let n_digest = Digest::from(state.finalize());
    assert_eq!(Some(n_digest), p.value_hash(IdTreeObjId(1), N * K));

    let v = query_without_proof(N * K, &id_tree, id_tree.root_id, IdTreeObjId(2)).unwrap();
    let mut o3_keywords: HashSet<String> = HashSet::new();
    o3_keywords.insert("c".to_string());
    let o3: Object<i32> = Object::new_dbg(ObjId(2), BlockId(1), vec![7], o3_keywords);
    let o3_digest = o3.to_digest();
    assert_eq!(Some(o3_digest), v);
    let (v, p) = query_id_tree(N * K, &id_tree, id_tree.root_id, IdTreeObjId(2)).unwrap();
    assert_eq!(Some(o3_digest), v);
    assert_eq!(
        id_tree
            .load_node(id_tree.root_id)
            .unwrap()
            .unwrap()
            .to_digest(),
        p.root_hash()
    );
    let mut state = blake2().to_state();
    state.update(&IdTreeObjId(2).to_le_bytes());
    state.update(o3_digest.as_bytes());
    let n_digest = Digest::from(state.finalize());
    assert_eq!(Some(n_digest), p.value_hash(IdTreeObjId(2), N * K));
}

#[test]
fn test_read_ctx1() {
    let id_tree = build_test_id_tree1();
    //println!("{:?}", id_tree);
    let mut ctx1 = ReadContext::new(&id_tree, id_tree.root_id);

    let mut o1_keywords: HashSet<String> = HashSet::new();
    o1_keywords.insert("a".to_string());
    let o1: Object<i32> = Object::new_dbg(ObjId(0), BlockId(1), vec![2], o1_keywords);
    let o1_digest = o1.to_digest();
    let mut o2_keywords: HashSet<String> = HashSet::new();
    o2_keywords.insert("b".to_string());
    let o2: Object<i32> = Object::new_dbg(ObjId(1), BlockId(1), vec![3], o2_keywords);
    let o2_digest = o2.to_digest();
    let mut o3_keywords: HashSet<String> = HashSet::new();
    o3_keywords.insert("c".to_string());
    let o3: Object<i32> = Object::new_dbg(ObjId(2), BlockId(1), vec![7], o3_keywords);
    let o3_digest = o3.to_digest();

    let v = ctx1.query(N * K, IdTreeObjId(11)).unwrap();
    assert_eq!(None, v);
    let v = ctx1.query(N * K, IdTreeObjId(0)).unwrap();
    assert_eq!(Some(o1_digest), v);
    println!("{:?}", ctx1.get_proof());
    let v = ctx1.query(N * K, IdTreeObjId(1)).unwrap();
    assert_eq!(Some(o2_digest), v);
    let v = ctx1.query(N * K, IdTreeObjId(2)).unwrap();
    assert_eq!(Some(o3_digest), v);
    let p = ctx1.into_proof();
    println!("ctx proof after querying 0: {:?}", p);
    assert_eq!(
        id_tree
            .load_node(id_tree.root_id)
            .unwrap()
            .unwrap()
            .to_digest(),
        p.root_hash()
    );
    assert!(p.value_hash(IdTreeObjId(11), N * K).unwrap().is_zero());

    let mut state = blake2().to_state();
    state.update(&IdTreeObjId(0).to_le_bytes());
    state.update(o1_digest.as_bytes());
    let n1_digest = Digest::from(state.finalize());
    assert_eq!(Some(n1_digest), p.value_hash(IdTreeObjId(0), N * K));

    let mut state = blake2().to_state();
    state.update(&IdTreeObjId(1).to_le_bytes());
    state.update(o2_digest.as_bytes());
    let n2_digest = Digest::from(state.finalize());
    assert_eq!(Some(n2_digest), p.value_hash(IdTreeObjId(1), N * K));

    let mut state = blake2().to_state();
    state.update(&IdTreeObjId(2).to_le_bytes());
    state.update(o3_digest.as_bytes());
    let n3_digest = Digest::from(state.finalize());
    assert_eq!(Some(n3_digest), p.value_hash(IdTreeObjId(2), N * K));
    //assert_eq!(Some(Digest::zero()), p.value_hash(IdTreeObjId(0), N * K));
}
