use super::{
    read::ReadContext, write::Apply, write::WriteContext, TrieNode, TrieNodeId, TrieNodeLoader,
};
use crate::{
    acc::{AccValue, Set},
    chain::{
        id_tree::ObjId,
        tests::PUB_KEY,
        trie_tree::{read::query_trie, TrieRoot},
    },
    digest::Digestible,
    set,
};
use anyhow::{bail, Result};
use std::{collections::HashMap, num::NonZeroU64};

#[derive(Debug, Default, Clone, Eq, PartialEq)]
struct TestTrie {
    root_id: Option<TrieNodeId>,
    nodes: HashMap<TrieNodeId, TrieNode>,
}

impl TrieNodeLoader for TestTrie {
    fn load_node(&self, id: TrieNodeId) -> Result<TrieNode> {
        match self.nodes.get(&id).cloned() {
            Some(n) => Ok(n),
            None => bail!("Cannot find node in TestTrie"),
        }
    }
}

impl TrieNodeLoader for &'_ TestTrie {
    fn load_node(&self, id: TrieNodeId) -> Result<TrieNode> {
        match self.nodes.get(&id).cloned() {
            Some(n) => Ok(n),
            None => bail!("Cannot find node in TestTrie"),
        }
    }
}

impl TestTrie {
    pub fn new() -> Self {
        Self {
            root_id: None,
            nodes: HashMap::new(),
        }
    }

    fn apply(&mut self, apply: Apply) {
        self.root_id = apply.root.trie_root_id;
        self.nodes.extend(apply.nodes.into_iter());
    }
}

pub fn set_root_id(trie_root: &mut TrieRoot, id: Option<TrieNodeId>) {
    trie_root.trie_root_id = id;
}

fn get_dataset() -> Vec<(String, NonZeroU64)> {
    unsafe {
        let data: Vec<(String, NonZeroU64)> = vec![
            ("abcd".to_string(), NonZeroU64::new_unchecked(1)),
            ("abcde".to_string(), NonZeroU64::new_unchecked(2)),
            ("abca".to_string(), NonZeroU64::new_unchecked(3)),
            ("abcd".to_string(), NonZeroU64::new_unchecked(4)),
            ("abc".to_string(), NonZeroU64::new_unchecked(5)),
            ("abcb".to_string(), NonZeroU64::new_unchecked(6)),
            ("abdef".to_string(), NonZeroU64::new_unchecked(7)),
            ("a".to_string(), NonZeroU64::new_unchecked(8)),
            ("bcd".to_string(), NonZeroU64::new_unchecked(9)),
            ("bce".to_string(), NonZeroU64::new_unchecked(10)),
        ];
        data
    }
}

#[test]
fn test_write() {
    let data = get_dataset();
    let mut test_trie = TestTrie::new();
    let mut test_trie_root = TrieRoot::default();
    set_root_id(&mut test_trie_root, test_trie.root_id);
    let mut ctx = WriteContext::new(&test_trie, test_trie_root);
    for i in 0..10 {
        let data = &data[i];
        ctx.insert(data.0.clone(), ObjId(data.1), &PUB_KEY).unwrap();
    }
    unsafe {
        ctx.delete(
            "abcd".to_string(),
            ObjId(NonZeroU64::new_unchecked(4)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            "abcd".to_string(),
            ObjId(NonZeroU64::new_unchecked(1)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            "bce".to_string(),
            ObjId(NonZeroU64::new_unchecked(10)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            "abcb".to_string(),
            ObjId(NonZeroU64::new_unchecked(6)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            "abc".to_string(),
            ObjId(NonZeroU64::new_unchecked(5)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            "a".to_string(),
            ObjId(NonZeroU64::new_unchecked(8)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            "bcd".to_string(),
            ObjId(NonZeroU64::new_unchecked(9)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            "abdef".to_string(),
            ObjId(NonZeroU64::new_unchecked(7)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            "abca".to_string(),
            ObjId(NonZeroU64::new_unchecked(3)),
            &PUB_KEY,
        )
        .unwrap();
    }
    let change = ctx.changes();
    test_trie.apply(change);
    assert_eq!(1, 1);
}

#[test]
fn test_read() {
    let data = get_dataset();
    let mut test_trie = TestTrie::new();
    let mut test_trie_root = TrieRoot::default();
    set_root_id(&mut test_trie_root, test_trie.root_id);
    let mut ctx = WriteContext::new(&test_trie, test_trie_root);
    for i in 0..10 {
        let data = &data[i];
        ctx.insert(data.0.clone(), ObjId(data.1), &PUB_KEY).unwrap();
    }
    let change = ctx.changes();
    test_trie.apply(change);

    let empty_set = Set::new();
    let empty_acc = AccValue::from_set(&empty_set, &PUB_KEY);
    let keyword = "fge".to_string();
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, keyword, &PUB_KEY).unwrap();
    assert_eq!(s, empty_set);
    assert_eq!(a, empty_acc);
    assert_eq!(
        test_trie
            .load_node(test_trie.root_id.unwrap())
            .unwrap()
            .to_digest(),
        p.root_hash()
    );

    let expect_set = set! {1, 4};
    let expect_acc = AccValue::from_set(&expect_set, &PUB_KEY);
    let keyword = "abcd".to_string();
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, keyword, &PUB_KEY).unwrap();
    assert_eq!(s, expect_set);
    assert_eq!(a, expect_acc);
    assert_eq!(
        test_trie
            .load_node(test_trie.root_id.unwrap())
            .unwrap()
            .to_digest(),
        p.root_hash()
    );

    let expect_set = set! {10};
    let expect_acc = AccValue::from_set(&expect_set, &PUB_KEY);
    let keyword = "bce".to_string();
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, keyword, &PUB_KEY).unwrap();
    assert_eq!(s, expect_set);
    assert_eq!(a, expect_acc);
    assert_eq!(
        test_trie
            .load_node(test_trie.root_id.unwrap())
            .unwrap()
            .to_digest(),
        p.root_hash()
    );

    let expect_set = set! {6};
    let expect_acc = AccValue::from_set(&expect_set, &PUB_KEY);
    let keyword = "abcb".to_string();
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, keyword, &PUB_KEY).unwrap();
    assert_eq!(s, expect_set);
    assert_eq!(a, expect_acc);
    assert_eq!(
        test_trie
            .load_node(test_trie.root_id.unwrap())
            .unwrap()
            .to_digest(),
        p.root_hash()
    );

    let expect_set = set! {5};
    let expect_acc = AccValue::from_set(&expect_set, &PUB_KEY);
    let keyword = "abc".to_string();
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, keyword, &PUB_KEY).unwrap();
    assert_eq!(s, expect_set);
    assert_eq!(a, expect_acc);
    assert_eq!(
        test_trie
            .load_node(test_trie.root_id.unwrap())
            .unwrap()
            .to_digest(),
        p.root_hash()
    );

    let expect_set = set! {8};
    let expect_acc = AccValue::from_set(&expect_set, &PUB_KEY);
    let keyword = "a".to_string();
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, keyword, &PUB_KEY).unwrap();
    assert_eq!(s, expect_set);
    assert_eq!(a, expect_acc);
    assert_eq!(
        test_trie
            .load_node(test_trie.root_id.unwrap())
            .unwrap()
            .to_digest(),
        p.root_hash()
    );

    let expect_set = set! {9};
    let expect_acc = AccValue::from_set(&expect_set, &PUB_KEY);
    let keyword = "bcd".to_string();
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, keyword, &PUB_KEY).unwrap();
    assert_eq!(s, expect_set);
    assert_eq!(a, expect_acc);
    assert_eq!(
        test_trie
            .load_node(test_trie.root_id.unwrap())
            .unwrap()
            .to_digest(),
        p.root_hash()
    );

    let expect_set = set! {7};
    let expect_acc = AccValue::from_set(&expect_set, &PUB_KEY);
    let keyword = "abdef".to_string();
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, keyword, &PUB_KEY).unwrap();
    assert_eq!(s, expect_set);
    assert_eq!(a, expect_acc);
    assert_eq!(
        test_trie
            .load_node(test_trie.root_id.unwrap())
            .unwrap()
            .to_digest(),
        p.root_hash()
    );

    let expect_set = set! {3};
    let expect_acc = AccValue::from_set(&expect_set, &PUB_KEY);
    let keyword = "abca".to_string();
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, keyword, &PUB_KEY).unwrap();
    assert_eq!(s, expect_set);
    assert_eq!(a, expect_acc);
    assert_eq!(
        test_trie
            .load_node(test_trie.root_id.unwrap())
            .unwrap()
            .to_digest(),
        p.root_hash()
    );
}

#[test]
fn test_read_ctx() {
    let data = get_dataset();
    let mut test_trie = TestTrie::new();
    let mut test_trie_root = TrieRoot::default();
    set_root_id(&mut test_trie_root, test_trie.root_id);
    let mut ctx = WriteContext::new(&test_trie, test_trie_root);
    for i in 0..10 {
        let data = &data[i];
        ctx.insert(data.0.clone(), ObjId(data.1), &PUB_KEY).unwrap();
    }
    let change = ctx.changes();
    test_trie.apply(change);

    let empty_set = Set::new();
    let empty_acc = AccValue::from_set(&empty_set, &PUB_KEY);
    let expect_set1 = set! {1, 4};
    let expect_acc1 = AccValue::from_set(&expect_set1, &PUB_KEY);
    let expect_set2 = set! {6};
    let expect_acc2 = AccValue::from_set(&expect_set2, &PUB_KEY);
    let expect_set3 = set! {10};
    let expect_acc3 = AccValue::from_set(&expect_set3, &PUB_KEY);
    let expect_set4 = set! {5};
    let expect_acc4 = AccValue::from_set(&expect_set4, &PUB_KEY);
    let expect_set5 = set! {8};
    let expect_acc5 = AccValue::from_set(&expect_set5, &PUB_KEY);
    let expect_set6 = set! {9};
    let expect_acc6 = AccValue::from_set(&expect_set6, &PUB_KEY);
    let expect_set7 = set! {7};
    let expect_acc7 = AccValue::from_set(&expect_set7, &PUB_KEY);
    let expect_set8 = set! {3};
    let expect_acc8 = AccValue::from_set(&expect_set8, &PUB_KEY);
    let expect_set9 = set! {2};
    let expect_acc9 = AccValue::from_set(&expect_set9, &PUB_KEY);

    let mut ctx = ReadContext::new(&test_trie, test_trie.root_id);
    let (s, a) = ctx.query("befg".to_string(), &PUB_KEY).unwrap();
    assert_eq!(s, empty_set);
    assert_eq!(a, empty_acc);
    let (s, a) = ctx.query("cefg".to_string(), &PUB_KEY).unwrap();
    assert_eq!(s, empty_set);
    assert_eq!(a, empty_acc);
    let (s, a) = ctx.query("abcd".to_string(), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set1);
    assert_eq!(a, expect_acc1);
    let (s, a) = ctx.query("abcb".to_string(), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set2);
    assert_eq!(a, expect_acc2);
    let (s, a) = ctx.query("bce".to_string(), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set3);
    assert_eq!(a, expect_acc3);
    let (s, a) = ctx.query("abc".to_string(), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set4);
    assert_eq!(a, expect_acc4);
    let (s, a) = ctx.query("a".to_string(), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set5);
    assert_eq!(a, expect_acc5);
    let (s, a) = ctx.query("bcd".to_string(), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set6);
    assert_eq!(a, expect_acc6);
    let (s, a) = ctx.query("abdef".to_string(), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set7);
    assert_eq!(a, expect_acc7);
    let (s, a) = ctx.query("abca".to_string(), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set8);
    assert_eq!(a, expect_acc8);
    let (s, a) = ctx.query("abcde".to_string(), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set9);
    assert_eq!(a, expect_acc9);

    let p = ctx.into_proof();
    assert_eq!(
        test_trie
            .load_node(test_trie.root_id.unwrap())
            .unwrap()
            .to_digest(),
        p.root_hash()
    );

    p.verify_acc(empty_acc, "befg".to_string(), &PUB_KEY)
        .unwrap();
    p.verify_acc(empty_acc, "cefg".to_string(), &PUB_KEY)
        .unwrap();
    p.verify_acc(expect_acc1, "abcd".to_string(), &PUB_KEY)
        .unwrap();
    p.verify_acc(expect_acc2, "abcb".to_string(), &PUB_KEY)
        .unwrap();
    p.verify_acc(expect_acc3, "bce".to_string(), &PUB_KEY)
        .unwrap();
    p.verify_acc(expect_acc4, "abc".to_string(), &PUB_KEY)
        .unwrap();
    p.verify_acc(expect_acc5, "a".to_string(), &PUB_KEY)
        .unwrap();
    p.verify_acc(expect_acc6, "bcd".to_string(), &PUB_KEY)
        .unwrap();
    p.verify_acc(expect_acc7, "abdef".to_string(), &PUB_KEY)
        .unwrap();
    p.verify_acc(expect_acc8, "abca".to_string(), &PUB_KEY)
        .unwrap();
    p.verify_acc(expect_acc9, "abcde".to_string(), &PUB_KEY)
        .unwrap();
}
