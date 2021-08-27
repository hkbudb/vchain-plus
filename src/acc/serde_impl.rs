use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use core::marker::PhantomData;
use serde::{
    de::{Deserializer, Visitor},
    ser::Serializer,
};

pub fn serialize<S: Serializer, T: CanonicalSerialize>(t: &T, s: S) -> Result<S::Ok, S::Error> {
    let mut buf = Vec::<u8>::new();
    t.serialize(&mut buf)
        .map_err(<S::Error as serde::ser::Error>::custom)?;
    if s.is_human_readable() {
        s.serialize_str(&hex::encode(&buf))
    } else {
        s.serialize_bytes(&buf)
    }
}

pub fn deserialize<'de, D: Deserializer<'de>, T: CanonicalDeserialize>(
    d: D,
) -> Result<T, D::Error> {
    use core::fmt;
    use serde::de::Error as DeError;

    struct HexVisitor<T>(PhantomData<T>);

    impl<'de, T: CanonicalDeserialize> Visitor<'de> for HexVisitor<T> {
        type Value = T;

        fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("T: CanonicalDeserialize")
        }

        fn visit_str<E: DeError>(self, value: &str) -> Result<T, E> {
            let data = hex::decode(value).map_err(E::custom)?;
            T::deserialize(&data[..]).map_err(E::custom)
        }
    }

    struct BytesVisitor<T>(PhantomData<T>);

    impl<'de, T: CanonicalDeserialize> Visitor<'de> for BytesVisitor<T> {
        type Value = T;

        fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("T: CanonicalDeserialize")
        }

        fn visit_bytes<E: DeError>(self, v: &[u8]) -> Result<T, E> {
            T::deserialize(v).map_err(E::custom)
        }
    }

    if d.is_human_readable() {
        d.deserialize_str(HexVisitor(PhantomData))
    } else {
        d.deserialize_bytes(BytesVisitor(PhantomData))
    }
}

pub mod unchecked {
    use super::*;

    pub fn serialize<S: Serializer, T: CanonicalSerialize>(t: &T, s: S) -> Result<S::Ok, S::Error> {
        let mut buf = Vec::<u8>::new();
        t.serialize_unchecked(&mut buf)
            .map_err(<S::Error as serde::ser::Error>::custom)?;
        if s.is_human_readable() {
            s.serialize_str(&hex::encode(&buf))
        } else {
            s.serialize_bytes(&buf)
        }
    }

    pub fn deserialize<'de, D: Deserializer<'de>, T: CanonicalDeserialize>(
        d: D,
    ) -> Result<T, D::Error> {
        use core::fmt;
        use serde::de::Error as DeError;

        struct HexVisitor<T>(PhantomData<T>);

        impl<'de, T: CanonicalDeserialize> Visitor<'de> for HexVisitor<T> {
            type Value = T;

            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str("T: CanonicalDeserialize")
            }

            fn visit_str<E: DeError>(self, value: &str) -> Result<T, E> {
                let data = hex::decode(value).map_err(E::custom)?;
                T::deserialize_unchecked(&data[..]).map_err(E::custom)
            }
        }

        struct BytesVisitor<T>(PhantomData<T>);

        impl<'de, T: CanonicalDeserialize> Visitor<'de> for BytesVisitor<T> {
            type Value = T;

            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str("T: CanonicalDeserialize")
            }

            fn visit_bytes<E: DeError>(self, v: &[u8]) -> Result<T, E> {
                T::deserialize_unchecked(v).map_err(E::custom)
            }
        }

        if d.is_human_readable() {
            d.deserialize_str(HexVisitor(PhantomData))
        } else {
            d.deserialize_bytes(BytesVisitor(PhantomData))
        }
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{G1Affine, G2Affine};
    use ark_ec::AffineCurve;
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
    struct Foo {
        #[serde(with = "super")]
        f1: G1Affine,
        #[serde(with = "super")]
        f2: G2Affine,
    }

    #[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
    struct Bar {
        #[serde(with = "super::unchecked")]
        f1: G1Affine,
        #[serde(with = "super::unchecked")]
        f2: G2Affine,
    }

    #[test]
    fn test_serde() {
        #[allow(clippy::blacklisted_name)]
        let foo = Foo {
            f1: G1Affine::prime_subgroup_generator(),
            f2: G2Affine::prime_subgroup_generator(),
        };

        let json = serde_json::to_string_pretty(&foo).unwrap();
        let bin = bincode::serialize(&foo).unwrap();

        assert_eq!(serde_json::from_str::<Foo>(&json).unwrap(), foo);
        assert_eq!(bincode::deserialize::<Foo>(&bin[..]).unwrap(), foo);
    }

    #[test]
    fn test_serde_unchecked() {
        #[allow(clippy::blacklisted_name)]
        let bar = Bar {
            f1: G1Affine::prime_subgroup_generator(),
            f2: G2Affine::prime_subgroup_generator(),
        };

        let json = serde_json::to_string_pretty(&bar).unwrap();
        let bin = bincode::serialize(&bar).unwrap();

        assert_eq!(serde_json::from_str::<Bar>(&json).unwrap(), bar);
        assert_eq!(bincode::deserialize::<Bar>(&bin[..]).unwrap(), bar);
    }
}
