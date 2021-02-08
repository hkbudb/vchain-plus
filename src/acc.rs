//! Ref: http://users.umiacs.umd.edu/~zhangyp/papers/accum.pdf

pub mod acc_values;
pub mod keys;
pub mod serde_impl;
pub mod set;
pub mod utils;

use ark_bls12_381::Bls12_381;
pub type AccSecretKey = keys::AccSecretKey<Bls12_381>;
pub type AccPublicKey = keys::AccPublicKey<Bls12_381>;
pub type LeftAccValue = acc_values::LeftAccValue<Bls12_381>;
pub type RightAccValue = acc_values::RightAccValue<Bls12_381>;
pub type AccValue = acc_values::AccValue<Bls12_381>;
