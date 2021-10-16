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
use smol_str::SmolStr;
use std::{collections::HashMap, num::NonZeroU16};

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

fn get_dataset() -> Vec<(String, NonZeroU16)> {
    unsafe {
        let data: Vec<(String, NonZeroU16)> = vec![
            ("abcd".to_string(), NonZeroU16::new_unchecked(1)),
            ("abcde".to_string(), NonZeroU16::new_unchecked(2)),
            ("abca".to_string(), NonZeroU16::new_unchecked(3)),
            ("abcd".to_string(), NonZeroU16::new_unchecked(4)),
            ("abc".to_string(), NonZeroU16::new_unchecked(5)),
            ("abcb".to_string(), NonZeroU16::new_unchecked(6)),
            ("abdef".to_string(), NonZeroU16::new_unchecked(7)),
            ("a".to_string(), NonZeroU16::new_unchecked(8)),
            ("bcd".to_string(), NonZeroU16::new_unchecked(9)),
            ("bce".to_string(), NonZeroU16::new_unchecked(10)),
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
        ctx.insert(SmolStr::from(data.0.clone()), ObjId(data.1), &PUB_KEY)
            .unwrap();
    }
    unsafe {
        ctx.delete(
            SmolStr::from("abcd"),
            ObjId(NonZeroU16::new_unchecked(4)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            SmolStr::from("abcd"),
            ObjId(NonZeroU16::new_unchecked(1)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            SmolStr::from("bce"),
            ObjId(NonZeroU16::new_unchecked(10)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            SmolStr::from("abcb"),
            ObjId(NonZeroU16::new_unchecked(6)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            SmolStr::from("abc"),
            ObjId(NonZeroU16::new_unchecked(5)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            SmolStr::from("a"),
            ObjId(NonZeroU16::new_unchecked(8)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            SmolStr::from("bcd"),
            ObjId(NonZeroU16::new_unchecked(9)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            SmolStr::from("abdef"),
            ObjId(NonZeroU16::new_unchecked(7)),
            &PUB_KEY,
        )
        .unwrap();
        ctx.delete(
            SmolStr::from("abca"),
            ObjId(NonZeroU16::new_unchecked(3)),
            &PUB_KEY,
        )
        .unwrap();
    }
    let change = ctx.changes();
    test_trie.apply(change);
    let trie_root_id = test_trie.root_id.unwrap();
    let trie_root = test_trie.load_node(trie_root_id).unwrap();
    let trie_root_set = trie_root.get_set();
    let test_acc = AccValue::from_set(trie_root_set, &PUB_KEY);
    let trie_root_acc = *trie_root.get_acc();
    assert_eq!(test_acc, trie_root_acc);
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
        ctx.insert(SmolStr::from(data.0.clone()), ObjId(data.1), &PUB_KEY)
            .unwrap();
    }
    let change = ctx.changes();
    test_trie.apply(change);

    let empty_set = Set::new();
    let empty_acc = AccValue::from_set(&empty_set, &PUB_KEY);
    let keyword = SmolStr::from("fge");
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, &keyword, &PUB_KEY).unwrap();
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
    let keyword = SmolStr::from("abcd");
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, &keyword, &PUB_KEY).unwrap();
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
    let keyword = SmolStr::from("bce");
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, &keyword, &PUB_KEY).unwrap();
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
    let keyword = SmolStr::from("abcb");
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, &keyword, &PUB_KEY).unwrap();
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
    let keyword = SmolStr::from("abc");
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, &keyword, &PUB_KEY).unwrap();
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
    let keyword = SmolStr::from("a");
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, &keyword, &PUB_KEY).unwrap();
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
    let keyword = SmolStr::from("bcd");
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, &keyword, &PUB_KEY).unwrap();
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
    let keyword = SmolStr::from("abdef");
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, &keyword, &PUB_KEY).unwrap();
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
    let keyword = SmolStr::from("abca");
    let (s, a, p) = query_trie(&test_trie, test_trie.root_id, &keyword, &PUB_KEY).unwrap();
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
        ctx.insert(SmolStr::from(data.0.clone()), ObjId(data.1), &PUB_KEY)
            .unwrap();
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
    let (s, a) = ctx.query(&SmolStr::from("befg"), &PUB_KEY).unwrap();
    assert_eq!(s, empty_set);
    assert_eq!(a, empty_acc);
    let (s, a) = ctx.query(&SmolStr::from("cefg"), &PUB_KEY).unwrap();
    assert_eq!(s, empty_set);
    assert_eq!(a, empty_acc);
    let (s, a) = ctx.query(&SmolStr::from("abcd"), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set1);
    assert_eq!(a, expect_acc1);
    let (s, a) = ctx.query(&SmolStr::from("abcb"), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set2);
    assert_eq!(a, expect_acc2);
    let (s, a) = ctx.query(&SmolStr::from("bce"), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set3);
    assert_eq!(a, expect_acc3);
    let (s, a) = ctx.query(&SmolStr::from("abc"), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set4);
    assert_eq!(a, expect_acc4);
    let (s, a) = ctx.query(&SmolStr::from("a"), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set5);
    assert_eq!(a, expect_acc5);
    let (s, a) = ctx.query(&SmolStr::from("bcd"), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set6);
    assert_eq!(a, expect_acc6);
    let (s, a) = ctx.query(&SmolStr::from("abdef"), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set7);
    assert_eq!(a, expect_acc7);
    let (s, a) = ctx.query(&SmolStr::from("abca"), &PUB_KEY).unwrap();
    assert_eq!(s, expect_set8);
    assert_eq!(a, expect_acc8);
    let (s, a) = ctx.query(&SmolStr::from("abcde"), &PUB_KEY).unwrap();
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

    p.verify_acc(empty_acc, "befg", &PUB_KEY).unwrap();
    p.verify_acc(empty_acc, "cefg", &PUB_KEY).unwrap();
    p.verify_acc(expect_acc1, "abcd", &PUB_KEY).unwrap();
    p.verify_acc(expect_acc2, "abcb", &PUB_KEY).unwrap();
    p.verify_acc(expect_acc3, "bce", &PUB_KEY).unwrap();
    p.verify_acc(expect_acc4, "abc", &PUB_KEY).unwrap();
    p.verify_acc(expect_acc5, "a", &PUB_KEY).unwrap();
    p.verify_acc(expect_acc6, "bcd", &PUB_KEY).unwrap();
    p.verify_acc(expect_acc7, "abdef", &PUB_KEY).unwrap();
    p.verify_acc(expect_acc8, "abca", &PUB_KEY).unwrap();
    p.verify_acc(expect_acc9, "abcde", &PUB_KEY).unwrap();
}

#[test]
fn test_common_prefix_len() {
    use super::common_prefix_len;

    let a = "abcde";
    let b = "abcfg";
    let common_prefix_len = common_prefix_len(a, b);
    let expect = 3 as usize;

    assert_eq!(common_prefix_len, expect);
}

#[test]
fn test_split_at_common_prefix2() {
    use super::split_at_common_prefix2;

    let a = "abcdef";
    let b = "abcfgh";
    let res = split_at_common_prefix2(a, b);
    let expect = (
        "abc".to_string(),
        'd',
        "ef".to_string(),
        'f',
        "gh".to_string(),
    );
    assert_eq!(res, expect);

    let a = "ecdef";
    let b = "abcfgh";
    let res = split_at_common_prefix2(a, b);
    let expect = (
        "".to_string(),
        'e',
        "cdef".to_string(),
        'a',
        "bcfgh".to_string(),
    );
    assert_eq!(res, expect);

    let a = "abcde";
    let b = "abcdf";
    let res = split_at_common_prefix2(a, b);
    let expect = ("abcd".to_string(), 'e', "".to_string(), 'f', "".to_string());
    assert_eq!(res, expect);

    let a = "abcde";
    let b = "";
    let res = split_at_common_prefix2(a, b);
    let expect = (
        "".to_string(),
        'a',
        "bcde".to_string(),
        '\0',
        "".to_string(),
    );

    assert_eq!(res, expect);
}

#[test]
fn test_box() {
    use crate::digest::Digestible;
    let a = "1".to_string();
    let b = Box::new(a.clone());
    assert_eq!(a.to_digest(), b.to_digest());
    assert_eq!(a.to_digest(), b.as_ref().to_digest());
}
