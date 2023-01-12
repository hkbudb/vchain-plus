use crate::{
    acc::{AccPublicKey, AccSecretKey},
    chain::{block::Height, object::Object, query::query_param::QueryParam, traits::Num},
};
use anyhow::{ensure, Context, Error, Result};
use howlong::ProcessDuration;
use memmap2::Mmap;
use rand::{CryptoRng, RngCore};
use serde::{Deserialize, Serialize};
use snap::{read::FrameDecoder, write::FrameEncoder};
use std::{
    collections::{BTreeMap, HashSet},
    error::Error as StdError,
    fs,
    fs::File,
    io::{prelude::*, BufReader},
    path::{Path, PathBuf},
    str::FromStr,
};
use tracing_subscriber::EnvFilter;

#[macro_export]
macro_rules! create_id_type_by_u32 {
    ($name: ident) => {
        #[derive(
            Debug,
            Default,
            Copy,
            Clone,
            Eq,
            PartialEq,
            Ord,
            PartialOrd,
            Hash,
            serde::Serialize,
            serde::Deserialize,
            derive_more::Deref,
            derive_more::DerefMut,
            derive_more::Display,
            derive_more::From,
            derive_more::Into,
        )]
        pub struct $name(pub u32);

        impl $name {
            pub fn next_id() -> Self {
                use core::sync::atomic::{AtomicU32, Ordering};
                static ID_CNT: AtomicU32 = AtomicU32::new(0);
                Self(ID_CNT.fetch_add(1, Ordering::SeqCst))
            }
        }
    };
}

#[macro_export]
macro_rules! create_id_type_by_u16 {
    ($name: ident) => {
        #[derive(
            Debug,
            Default,
            Copy,
            Clone,
            Eq,
            PartialEq,
            Ord,
            PartialOrd,
            Hash,
            serde::Serialize,
            serde::Deserialize,
            derive_more::Deref,
            derive_more::DerefMut,
            derive_more::Display,
            derive_more::From,
            derive_more::Into,
        )]
        pub struct $name(pub u16);

        impl $name {
            pub fn next_id() -> Self {
                use core::sync::atomic::{AtomicU16, Ordering};
                static ID_CNT: AtomicU16 = AtomicU16::new(0);
                Self(ID_CNT.fetch_add(1, Ordering::SeqCst))
            }
        }
    };
}

pub fn load_query_param_from_file(path: &Path) -> Result<Vec<QueryParam<u32>>> {
    let data = fs::read_to_string(path)?;
    let query_params: Vec<QueryParam<u32>> = serde_json::from_str(&data)?;
    Ok(query_params)
}

// input format: block_id sep [ v_data ] sep { w_data }
// sep = \t or space
// v_data = v_1 comma v_2 ...
// w_data = w_1 comma w_2 ...
pub fn load_raw_obj_from_file<K, ParseErr>(path: &Path) -> Result<BTreeMap<Height, Vec<Object<K>>>>
where
    K: Num + FromStr<Err = ParseErr>,
    ParseErr: StdError + Sync + Send + 'static,
{
    let mut reader = BufReader::new(File::open(path)?);
    let mut buf = String::new();
    reader.read_to_string(&mut buf)?;
    load_raw_obj_from_str(&buf)
}

pub fn load_raw_obj_from_str<K, ParseErr>(input: &str) -> Result<BTreeMap<Height, Vec<Object<K>>>>
where
    K: Num + FromStr<Err = ParseErr>,
    ParseErr: StdError + Sync + Send + 'static,
{
    let mut res = BTreeMap::new();
    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let mut split_str = line.splitn(3, |c| c == '[' || c == ']');
        let blk_height: Height = Height(
            split_str
                .next()
                .with_context(|| format!("failed to parse line {}", line))?
                .trim()
                .parse()?,
        );
        let v_data: Vec<K> = split_str
            .next()
            .with_context(|| format!("failed to parse line {}", line))?
            .trim()
            .split(',')
            .map(|s| s.trim())
            .filter(|s| !s.is_empty())
            .map(|s| s.parse::<K>().map_err(Error::from))
            .collect::<Result<_>>()?;
        let w_data: HashSet<String> = split_str
            .next()
            .with_context(|| format!("failed to parse line {}", line))?
            .trim()
            .replace('{', "")
            .replace('}', "")
            .split(',')
            .map(|s| s.trim().to_owned())
            .filter(|s| !s.is_empty())
            .collect();

        let raw_obj = Object::new(blk_height, v_data, w_data);
        res.entry(blk_height).or_insert_with(Vec::new).push(raw_obj);
    }
    Ok(res)
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct KeyPair {
    sk: AccSecretKey,
    pub pk: AccPublicKey,
}

impl KeyPair {
    pub fn gen(q: u64, mut rng: impl RngCore + CryptoRng) -> Self {
        let sk = AccSecretKey::rand(&mut rng);
        let sk_with_pow = sk.into();
        let pk = AccPublicKey::gen_key(&sk_with_pow, q);
        Self { sk, pk }
    }

    pub fn save(&self, path: impl AsRef<Path>) -> Result<()> {
        let path = path.as_ref();
        ensure!(!path.exists(), "{} already exists.", path.display());
        fs::create_dir_all(&path)?;
        let sk_f = File::create(&Self::sk_path(path))?;
        bincode::serialize_into(sk_f, &self.sk)?;
        let pk_f = File::create(&Self::pk_path(path))?;
        bincode::serialize_into(pk_f, &self.pk)?;
        Ok(())
    }

    pub fn load(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();
        let sk_file = File::open(Self::sk_path(path))?;
        let sk_reader = BufReader::new(sk_file);
        let sk: AccSecretKey = bincode::deserialize_from(sk_reader)?;
        let pk_file = File::open(Self::pk_path(path))?;
        let pk_data = unsafe { Mmap::map(&pk_file) }?;
        let pk: AccPublicKey = bincode::deserialize(&pk_data[..])?;
        Ok(Self { sk, pk })
    }

    fn sk_path(path: &Path) -> PathBuf {
        path.join("sk")
    }

    fn pk_path(path: &Path) -> PathBuf {
        path.join("pk")
    }
}

pub fn init_tracing_subscriber(directives: &str) -> Result<()> {
    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new(directives));
    tracing_subscriber::fmt()
        .with_env_filter(filter)
        .try_init()
        .map_err(Error::msg)
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct QueryTime {
    pub(crate) stage1: Time,
    pub(crate) stage2: Time,
    pub(crate) stage3: Time,
    pub(crate) stage4: Time,
    pub(crate) total: Time,
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct Time {
    real: u64,
    user: u64,
    sys: u64,
}

impl From<ProcessDuration> for Time {
    fn from(p_duration: ProcessDuration) -> Self {
        Self {
            real: p_duration.real.as_micros() as u64,
            user: p_duration.user.as_micros() as u64,
            sys: p_duration.system.as_micros() as u64,
        }
    }
}

pub fn binary_encode<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    let mut encoder = FrameEncoder::new(Vec::new());
    bincode::serialize_into(&mut encoder, value).map_err(Error::msg)?;
    Ok(encoder.into_inner()?)
}

pub fn binary_decode<T: for<'de> Deserialize<'de>>(bytes: &[u8]) -> Result<T> {
    let decoder = FrameDecoder::new(bytes);
    bincode::deserialize_from(decoder).map_err(Error::msg)
}

#[cfg(test)]
mod tests {
    use super::KeyPair;
    use crate::{
        acc::{compute_set_operation_final, compute_set_operation_intermediate, AccValue, Op},
        chain::{
            block::Height,
            object::Object,
            query::query_plan::{QPKeywordNode, QPNode, QPUnion},
        },
        digest::Digestible,
        set,
        utils::{binary_decode, binary_encode, load_raw_obj_from_str},
    };
    use petgraph::Graph;
    use std::collections::BTreeMap;

    #[test]
    fn test_create_id() {
        create_id_type_by_u32!(TestId);
        assert_eq!(TestId::next_id(), TestId(0));
        assert_eq!(TestId::next_id(), TestId(1));
        assert_eq!(TestId::next_id(), TestId(2));
    }

    #[test]
    fn test_load_raw_obj() {
        let input = "1\t[1,2]\t{a,b}\n2 [ 3, 4 ] { c, d, }\n2\t[ 5, 6 ]\t { e }\n";
        let expect = {
            let mut exp: BTreeMap<Height, Vec<Object<u32>>> = BTreeMap::new();
            exp.insert(
                Height(1),
                vec![Object {
                    blk_height: Height(1),
                    num_data: vec![1, 2],
                    keyword_data: ["a".to_owned(), "b".to_owned()].iter().cloned().collect(),
                }],
            );
            exp.insert(
                Height(2),
                vec![
                    Object {
                        blk_height: Height(2),
                        num_data: vec![3, 4],
                        keyword_data: ["c".to_owned(), "d".to_owned()].iter().cloned().collect(),
                    },
                    Object {
                        blk_height: Height(2),
                        num_data: vec![5, 6],
                        keyword_data: ["e".to_owned()].iter().cloned().collect(),
                    },
                ],
            );
            exp
        };
        assert_eq!(load_raw_obj_from_str(&input).unwrap(), expect);
    }

    #[test]
    fn test_maintain_key() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("key");

        let q: u64 = 10;
        let rng = rand::thread_rng();
        let key_pair = KeyPair::gen(q, rng);
        key_pair.save(path.clone()).unwrap();

        let read_key_pair = KeyPair::load(&path).unwrap();
        assert_eq!(key_pair, read_key_pair);
    }

    #[test]
    fn test_petgraph_serialize() {
        let k1 = QPKeywordNode {
            blk_height: Height(0),
            set: None,
        };
        let k2 = QPKeywordNode {
            blk_height: Height(0),
            set: None,
        };
        let k3 = QPKeywordNode {
            blk_height: Height(0),
            set: None,
        };
        let k4 = QPKeywordNode {
            blk_height: Height(0),
            set: None,
        };
        let union = QPUnion { set: None };

        let mut qp_dag = Graph::<QPNode<u32>, bool>::new();
        let idx0 = qp_dag.add_node(QPNode::Keyword(Box::new(k1.clone())));
        let idx1 = qp_dag.add_node(QPNode::Keyword(Box::new(k2.clone())));
        let idx2 = qp_dag.add_node(QPNode::Keyword(Box::new(k3.clone())));
        let idx3 = qp_dag.add_node(QPNode::Keyword(Box::new(k4.clone())));
        let idx4 = qp_dag.add_node(QPNode::Union(union.clone()));
        let idx5 = qp_dag.add_node(QPNode::Union(union.clone()));
        let idx6 = qp_dag.add_node(QPNode::Union(union.clone()));

        qp_dag.add_edge(idx4, idx0, true);
        qp_dag.add_edge(idx4, idx1, false);
        qp_dag.add_edge(idx5, idx2, true);
        qp_dag.add_edge(idx5, idx3, false);
        qp_dag.add_edge(idx6, idx4, true);
        qp_dag.add_edge(idx6, idx5, false);

        let size_original = bincode::serialize(&qp_dag).unwrap().len();
        qp_dag.remove_node(idx0);
        qp_dag.remove_node(idx1);
        qp_dag.remove_node(idx2);
        qp_dag.remove_node(idx3);
        let size_update = bincode::serialize(&qp_dag).unwrap().len();
        println!("before: {}", size_original);
        println!("after: {}", size_update);
        assert_eq!(1, 1);
    }

    #[test]
    fn test_compress() {
        let value = String::from("hello world");
        let bin = binary_encode(&value).unwrap();
        assert_eq!(binary_decode::<String>(bin.as_ref()).unwrap(), value);
    }

    #[test]
    fn test_acc_size() {
        use crate::chain::tests::PUB_KEY;
        let set = set! {11, 12, 13, 14, 15, 16, 17, 19, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39};
        let acc = AccValue::from_set(&set, &PUB_KEY);
        let acc_size = bincode::serialize(&acc).unwrap().len();
        let dig = acc.to_digest();
        let dig_size = bincode::serialize(&dig).unwrap().len();
        assert_eq!(dig_size, 32);
        assert_eq!(acc_size, 416);
    }

    #[test]
    fn test_proof_size() {
        use crate::chain::tests::PUB_KEY;
        let set1 = set! {11, 17, 19, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30};
        let set2 = set! {12, 13, 14, 15, 16, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 33, 23, };
        let acc1 = AccValue::from_set(&set1, &PUB_KEY);
        let acc2 = AccValue::from_set(&set2, &PUB_KEY);
        let (_set, _acc, inter_proof) =
            compute_set_operation_intermediate(Op::Union, &set1, &acc1, &set2, &acc2, &PUB_KEY);
        let (_set, final_proof) = compute_set_operation_final(Op::Union, &set1, &set2, &PUB_KEY);
        let inter_size = bincode::serialize(&inter_proof).unwrap().len();
        let final_size = bincode::serialize(&final_proof).unwrap().len();
        assert_eq!(inter_size, 564);
        assert_eq!(final_size, 204);
    }

    use serde::{Deserialize, Serialize};
    #[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
    struct TestId(u8);
    #[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
    struct TestId2(u64);

    #[test]
    fn test_int_size() {
        let a: u8 = 1;
        let b: u32 = 1;
        let c: u64 = 1;
        let a_size = bincode::serialize(&a).unwrap().len();
        let b_size = bincode::serialize(&b).unwrap().len();
        let c_size = bincode::serialize(&c).unwrap().len();
        assert_eq!(a_size, 1);
        assert_eq!(b_size, 4);
        assert_eq!(c_size, 8);
        let a = TestId(1);
        let b = TestId2(1);
        let a_size = bincode::serialize(&a).unwrap().len();
        let b_size = bincode::serialize(&b).unwrap().len();
        assert_eq!(a_size, 1);
        assert_eq!(b_size, 8);

        let c = Some(b);
        let d: Option<TestId2> = None;
        let c_size = bincode::serialize(&c).unwrap().len();
        let d_size = bincode::serialize(&d).unwrap().len();
        assert_eq!(c_size, 9);
        assert_eq!(d_size, 1);
    }

    #[test]
    fn test_str_size() {
        let a: smol_str::SmolStr = smol_str::SmolStr::from("");
        let str_size = bincode::serialize(&a).unwrap().len();
        assert_eq!(str_size, 8);
        let a: String = String::from("");
        let str_size = bincode::serialize(&a).unwrap().len();
        assert_eq!(str_size, 8);
        let a = String::from("53c79113311e8a8ec291d412d1572516d0356a5c3aced0b108e0ad04c440de78");
        let str_size = bincode::serialize(&a).unwrap().len();
        assert_eq!(str_size, 72);
        let a = smol_str::SmolStr::from(
            "53c79113311e8a8ec291d412d1572516d0356a5c3aced0b108e0ad04c440de78",
        );
        let str_size = bincode::serialize(&a).unwrap().len();
        assert_eq!(str_size, 72);
    }
}
