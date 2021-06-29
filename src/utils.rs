use crate::acc::AccPublicKey;
use crate::chain::{block::Height, object::Object, traits::Num};
use anyhow::{Context, Error, Result};
use ark_serialize::Read;
use std::error::Error as StdError;
use std::str::FromStr;
use std::{
    collections::{BTreeMap, HashSet},
    fs::File,
    io::BufReader,
    path::Path,
};

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
                .context(format!("failed to parse line {}", line))?
                .trim()
                .parse()?,
        );
        let v_data: Vec<K> = split_str
            .next()
            .context(format!("failed to parse line {}", line))?
            .trim()
            .split(',')
            .map(|s| s.trim())
            .filter(|s| !s.is_empty())
            .map(|s| s.parse::<K>().map_err(Error::from))
            .collect::<Result<_>>()?;
        let w_data: HashSet<String> = split_str
            .next()
            .context(format!("failed to parse line {}", line))?
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

pub fn read_pub_key() -> AccPublicKey {
    todo!()
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::{
        chain::{block::Height, object::Object},
        utils::load_raw_obj_from_str,
    };

    #[test]
    fn test_create_id() {
        create_id_type!(TestId);
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
}
