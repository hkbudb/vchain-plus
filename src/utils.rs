use crate::{
    acc::{AccPublicKey, AccSecretKey},
    chain::{block::Height, object::Object, query::query_param::QueryParam, traits::Num},
};
use anyhow::{ensure, Context, Error, Result};
use howlong::ProcessDuration;
use memmap2::Mmap;
use rand::{CryptoRng, RngCore};
use serde::{Deserialize, Serialize};
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
macro_rules! create_id_type {
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
        pub struct $name(pub u64);

        impl $name {
            pub fn next_id() -> Self {
                use core::sync::atomic::{AtomicU64, Ordering};
                static ID_CNT: AtomicU64 = AtomicU64::new(0);
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
        let sk_f = File::create(&Self::sk_path(&path))?;
        bincode::serialize_into(sk_f, &self.sk)?;
        let pk_f = File::create(&Self::pk_path(&path))?;
        bincode::serialize_into(pk_f, &self.pk)?;
        Ok(())
    }

    pub fn load(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();
        let sk_file = File::open(Self::sk_path(&path))?;
        let sk_reader = BufReader::new(sk_file);
        let sk: AccSecretKey = bincode::deserialize_from(sk_reader)?;
        let pk_file = File::open(Self::pk_path(&path))?;
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
    let filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new(directives.to_string()));
    tracing_subscriber::fmt()
        .with_env_filter(filter)
        .try_init()
        .map_err(Error::msg)
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

#[cfg(test)]
mod tests {
    use super::{load_query_param_from_file, KeyPair};
    use crate::{
        chain::{block::Height, object::Object, query::query_param::QueryParam},
        utils::load_raw_obj_from_str,
    };
    use serde_json::json;
    use std::{collections::BTreeMap, path::Path};

    #[test]
    fn test_create_id() {
        create_id_type!(TestId);
        assert_eq!(TestId::next_id(), TestId(0));
        assert_eq!(TestId::next_id(), TestId(1));
        assert_eq!(TestId::next_id(), TestId(2));
    }

    #[test]
    fn test_load_query_param() {
        let input = Path::new("./data/query/test1.json");
        let res = load_query_param_from_file(input).unwrap();
        let param1_data = json!({
            "start_blk": 1,
            "end_blk": 3,
            "range": [[1, 5], [2, 8]],
            "keyword_exp": {
                "or": [
                    {"input": "a"},
                    {"input": "b"}
                ]
            }
        });
        let param1: QueryParam<u32> = serde_json::from_value(param1_data).unwrap();
        assert_eq!(param1, res[0]);

        let param2_data = json!({
            "start_blk": 2,
            "end_blk": 4,
            "range": [(1, 7), (2, 9)],
            "keyword_exp": {
                "or": [
                    {"input": "a"},
                    {"and": [{"input": "b"}, {"input": "c"}]},
                ]
            },
        });
        let param2: QueryParam<u32> = serde_json::from_value(param2_data).unwrap();
        assert_eq!(param2, res[1]);
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
}
