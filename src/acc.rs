//! Ref: http://users.umiacs.umd.edu/~zhangyp/papers/accum.pdf

pub mod acc_value;
pub mod keys;
pub mod ops;
pub mod poly;
pub mod serde_impl;
pub mod set;
pub mod utils;

pub use set::Set;
pub use ops::Op;

use ark_bls12_381::Bls12_381;
pub type AccSecretKey = keys::AccSecretKey<Bls12_381>;
pub type AccSecretKeyWithPowCache = keys::AccSecretKeyWithPowCache<Bls12_381>;
pub type AccPublicKey = keys::AccPublicKey<Bls12_381>;
pub type AccValue = acc_value::AccValue<Bls12_381>;
pub type IntermediateProof = ops::IntermediateProof<Bls12_381>;
pub type FinalProof = ops::FinalProof<Bls12_381>;
