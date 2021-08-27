//! Ref: https://user.eng.umd.edu/~cpap/published/accumEUROSP2017.pdf

pub mod acc_value;
pub mod keys;
pub mod ops;
pub mod poly;
pub mod serde_impl;
pub mod set;
pub mod utils;

pub use ops::Op;
pub use set::Set;

use ark_bn254::Bn254 as Curve;
pub type AccSecretKey = keys::AccSecretKey<Curve>;
pub type AccSecretKeyWithPowCache = keys::AccSecretKeyWithPowCache<Curve>;
pub type AccPublicKey = keys::AccPublicKey<Curve>;
pub type AccValue = acc_value::AccValue<Curve>;
pub type IntermediateProof = ops::IntermediateProof<Curve>;
pub type FinalProof = ops::FinalProof<Curve>;

#[inline(always)]
pub fn compute_set_operation_intermediate(
    op: Op,
    lhs_set: &Set,
    lhs_acc: &AccValue,
    rhs_set: &Set,
    rhs_acc: &AccValue,
    pk: &AccPublicKey,
) -> (Set, AccValue, IntermediateProof) {
    ops::compute_set_operation_intermediate(op, lhs_set, lhs_acc, rhs_set, rhs_acc, pk)
}

#[inline(always)]
pub fn compute_set_operation_final(
    op: Op,
    lhs_set: &Set,
    rhs_set: &Set,
    pk: &AccPublicKey,
) -> (Set, FinalProof) {
    ops::compute_set_operation_final(op, lhs_set, rhs_set, pk)
}
