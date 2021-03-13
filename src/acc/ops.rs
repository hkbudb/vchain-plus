use super::{
    acc_value::{cal_acc_pk, AccValue},
    keys::AccPublicKey,
    poly::{
        poly_a, poly_b, poly_div, poly_mul, poly_remove_term, poly_variable_minus_one, Poly,
        Variable, R, S,
    },
    set::Set,
};
use anyhow::{ensure, Context as _, Result};
use ark_ec::{msm::VariableBaseMSM, PairingEngine, ProjectiveCurve};
use ark_ff::PrimeField;
use core::marker::PhantomData;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Set operation
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Op {
    Intersection,
    Union,
    Difference,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct IntersectionProof<E: PairingEngine> {
    #[serde(with = "super::serde_impl")]
    g_x: E::G1Affine,
    #[serde(with = "super::serde_impl")]
    g_x_beta: E::G1Affine,
    #[serde(with = "super::serde_impl")]
    q_x_y: E::G1Affine,
    #[serde(with = "super::serde_impl")]
    q_x_y_delta: E::G1Affine,
    #[serde(with = "super::serde_impl")]
    l_x: E::G1Affine,
    _marker: PhantomData<E>,
}

impl<E: PairingEngine> IntersectionProof<E> {
    fn new(
        set: &Set,
        q_poly: &Poly<E::Fr>,
        x: Variable,
        y: Variable,
        g: E::G1Affine,
        get_g_x_i: impl Fn(u64) -> E::G1Affine + Sync,
        get_g_beta_x_i: impl Fn(u64) -> E::G1Affine + Sync,
        get_g_x_i_y_j: impl Fn(u64, u64) -> E::G1Affine + Sync,
        get_g_delta_x_i_y_j: impl Fn(u64, u64) -> E::G1Affine + Sync,
    ) -> Self {
        let g_x = cal_acc_pk(set, &get_g_x_i);
        let g_x_beta = cal_acc_pk(set, &get_g_beta_x_i);
        let l_x = cal_acc_pk(set, |i| if i == 1 { g } else { get_g_x_i(i - 1) });

        let mut bases: Vec<_> = Vec::with_capacity(q_poly.terms.len());
        let mut delta_bases: Vec<_> = Vec::with_capacity(q_poly.terms.len());
        let mut scalars: Vec<_> = Vec::with_capacity(q_poly.terms.len());
        for (coeff, term) in &q_poly.terms {
            scalars.push(coeff.into_repr());
            let term_map: HashMap<Variable, usize> = term.iter().copied().collect();
            let i = term_map[&x] as u64;
            let j = term_map[&y] as u64;
            bases.push(get_g_x_i_y_j(i, j));
            delta_bases.push(get_g_delta_x_i_y_j(i, j));
        }

        let q_x_y = VariableBaseMSM::multi_scalar_mul(&bases[..], &scalars[..]).into_affine();
        let q_x_y_delta =
            VariableBaseMSM::multi_scalar_mul(&delta_bases[..], &scalars[..]).into_affine();

        Self {
            g_x,
            g_x_beta,
            q_x_y,
            q_x_y_delta,
            l_x,
            _marker: PhantomData,
        }
    }

    fn verify(
        &self,
        lhs_acc: E::G1Affine,
        rhs_acc: E::G2Affine,
        h: E::G2Affine,
        h_y_q: E::G2Affine,
        h_beta: E::G2Affine,
        h_delta: E::G2Affine,
        h_x: E::G2Affine,
    ) -> Result<()> {
        ensure!(
            E::pairing(lhs_acc, rhs_acc)
                == E::product_of_pairings(&[
                    (self.g_x.into(), h_y_q.into()),
                    (self.q_x_y.into(), h.into())
                ]),
            "e(A, B) != e(I, h^{y^q}) * e(Q_{x,y}, h)"
        );
        ensure!(
            E::pairing(self.g_x, h_beta) == E::pairing(self.g_x_beta, h),
            "e(I, h^{beta}) != e(I_{beta}, h)"
        );
        ensure!(
            E::pairing(self.q_x_y, h_delta) == E::pairing(self.q_x_y_delta, h),
            "e(Q_{x,y}, h^{delta}) != e(Q_{x,y,delta}, h)"
        );
        ensure!(
            E::pairing(self.g_x, h) == E::pairing(self.l_x, h_x),
            "e(I, h) != e(L, h^x)"
        );
        Ok(())
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntermediateProof<E: PairingEngine> {
    op: Op,
    inner_proof_r: IntersectionProof<E>,
    inner_proof_s: IntersectionProof<E>,
}

impl<E: PairingEngine> IntermediateProof<E> {
    pub fn new(op: Op, lhs_set: &Set, rhs_set: &Set, pk: &AccPublicKey<E>) -> Self {
        let intersection_set = lhs_set & rhs_set;
        let lhs_poly: Poly<E::Fr> = poly_a(lhs_set, S);
        let rhs_poly: Poly<E::Fr> = poly_b(rhs_set, R, S, pk.q);
        let q_poly = poly_remove_term(&poly_mul(&lhs_poly, &rhs_poly), S, pk.q);
        let inner_proof_r = IntersectionProof::new(
            &intersection_set,
            &q_poly,
            R,
            S,
            pk.g,
            |i| pk.get_g_r_i(i),
            |i| pk.get_g_beta_r_i(i),
            |i, j| pk.get_g_r_i_s_j(i, j),
            |i, j| pk.get_g_delta_r_i_s_j(i, j),
        );
        let inner_proof_s = IntersectionProof::new(
            &intersection_set,
            &q_poly,
            S,
            R,
            pk.g,
            |i| pk.get_g_s_i(i),
            |i| pk.get_g_beta_s_i(i),
            |i, j| pk.get_g_r_i_s_j(i, j),
            |i, j| pk.get_g_delta_r_i_s_j(i, j),
        );

        // TODO

        Self {
            op,
            inner_proof_r,
            inner_proof_s,
        }
    }

    pub fn verify(
        &self,
        lhs_acc: &AccValue<E>,
        rhs_acc: &AccValue<E>,
        result_acc: &AccValue<E>,
        pk: &AccPublicKey<E>,
    ) -> Result<()> {
        self.inner_proof_r
            .verify(
                lhs_acc.g_s,
                rhs_acc.h_r_s,
                pk.h,
                pk.h_s_q,
                pk.h_beta,
                pk.h_delta,
                pk.h_r,
            )
            .context("failed to verify the inner_proof_r.")?;
        self.inner_proof_s
            .verify(
                lhs_acc.g_r,
                rhs_acc.h_s_r,
                pk.h,
                pk.h_r_q,
                pk.h_beta,
                pk.h_delta,
                pk.h_s,
            )
            .context("failed to verify the inner_proof_s.")?;

        // TODO

        Ok(())
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FinalProof<E: PairingEngine> {
    op: Op,
    inner_proof: IntersectionProof<E>,
}

impl<E: PairingEngine> FinalProof<E> {
    pub fn new(op: Op, lhs_set: &Set, rhs_set: &Set, pk: &AccPublicKey<E>) -> Self {
        let lhs_poly: Poly<E::Fr> = poly_a(lhs_set, S);
        let rhs_poly: Poly<E::Fr> = poly_b(rhs_set, R, S, pk.q);
        let q_poly = poly_remove_term(&poly_mul(&lhs_poly, &rhs_poly), S, pk.q);
        let inner_proof = IntersectionProof::new(
            &(lhs_set & rhs_set),
            &q_poly,
            R,
            S,
            pk.g,
            |i| pk.get_g_r_i(i),
            |i| pk.get_g_beta_r_i(i),
            |i, j| pk.get_g_r_i_s_j(i, j),
            |i, j| pk.get_g_delta_r_i_s_j(i, j),
        );
        Self { op, inner_proof }
    }

    pub fn verify(
        &self,
        lhs_acc: &AccValue<E>,
        rhs_acc: &AccValue<E>,
        result_set: &Set,
        pk: &AccPublicKey<E>,
    ) -> Result<()> {
        self.inner_proof
            .verify(
                lhs_acc.g_s,
                rhs_acc.h_r_s,
                pk.h,
                pk.h_s_q,
                pk.h_beta,
                pk.h_delta,
                pk.h_r,
            )
            .context("failed to verify the inner_proof.")?;
        let result_acc = match self.op {
            Op::Intersection => self.inner_proof.g_x,
            Op::Union => lhs_acc.g_r + rhs_acc.g_r + (-self.inner_proof.g_x),
            Op::Difference => lhs_acc.g_r + (-self.inner_proof.g_x),
        };
        let expect_acc = cal_acc_pk(result_set, |i| pk.get_g_r_i(i));
        ensure!(result_acc == expect_acc, "acc(set) is invalid.");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{acc::keys::AccSecretKey, set};
    use ark_bls12_381::{Bls12_381, Fr};

    #[test]
    fn test_intersection_proof() {
        let mut rng = rand::thread_rng();
        let q = 10;
        let sk = AccSecretKey::<Bls12_381>::rand(&mut rng).into();
        let pk = AccPublicKey::<Bls12_381>::gen_key(&sk, q);

        let s1 = set! {1, 2, 3};
        let s2 = set! {1, 5};
        let s3 = set! {1};

        let s1_a_poly: Poly<Fr> = poly_a(&s1, S);
        let s2_b_poly: Poly<Fr> = poly_b(&s2, R, S, q);
        let q_poly = poly_remove_term(&poly_mul(&s1_a_poly, &s2_b_poly), S, q);

        let s1_acc = AccValue::from_set_sk(&s1, &sk, q);
        let s2_acc = AccValue::from_set_sk(&s2, &sk, q);

        let proof = IntersectionProof::<Bls12_381>::new(
            &s3,
            &q_poly,
            R,
            S,
            pk.g,
            |i| pk.get_g_r_i(i),
            |i| pk.get_g_beta_r_i(i),
            |i, j| pk.get_g_r_i_s_j(i, j),
            |i, j| pk.get_g_delta_r_i_s_j(i, j),
        );
        proof
            .verify(
                s1_acc.g_s,
                s2_acc.h_r_s,
                pk.h,
                pk.h_s_q,
                pk.h_beta,
                pk.h_delta,
                pk.h_r,
            )
            .unwrap();
    }

    #[test]
    fn test_intermediate_proof() {
        let mut rng = rand::thread_rng();
        let q = 10;
        let sk = AccSecretKey::<Bls12_381>::rand(&mut rng).into();
        let pk = AccPublicKey::<Bls12_381>::gen_key(&sk, q);

        let s1 = set! {1, 2, 3};
        let s2 = set! {1, 5};

        let s1_acc = AccValue::from_set_sk(&s1, &sk, q);
        let s2_acc = AccValue::from_set_sk(&s2, &sk, q);
        let intersection_acc = AccValue::from_set_sk(&set! {1}, &sk, q);
        let union_acc = AccValue::from_set_sk(&set! {1, 2, 3, 5}, &sk, q);
        let difference_acc = AccValue::from_set_sk(&set! {2, 3}, &sk, q);

        let intersection_proof = IntermediateProof::<Bls12_381>::new(Op::Intersection, &s1, &s2, &pk);
        intersection_proof
            .verify(&s1_acc, &s2_acc, &intersection_acc, &pk)
            .unwrap();
        let union_proof = IntermediateProof::<Bls12_381>::new(Op::Union, &s1, &s2, &pk);
        union_proof
            .verify(&s1_acc, &s2_acc, &union_acc, &pk)
            .unwrap();
        let diff_proof = IntermediateProof::<Bls12_381>::new(Op::Difference, &s1, &s2, &pk);
        diff_proof
            .verify(&s1_acc, &s2_acc, &difference_acc, &pk)
            .unwrap();
    }

    #[test]
    fn test_final_proof() {
        let mut rng = rand::thread_rng();
        let q = 10;
        let sk = AccSecretKey::<Bls12_381>::rand(&mut rng).into();
        let pk = AccPublicKey::<Bls12_381>::gen_key(&sk, q);

        let s1 = set! {1, 2, 3};
        let s2 = set! {1, 5};

        let s1_acc = AccValue::from_set_sk(&s1, &sk, q);
        let s2_acc = AccValue::from_set_sk(&s2, &sk, q);

        let intersection_proof = FinalProof::<Bls12_381>::new(Op::Intersection, &s1, &s2, &pk);
        intersection_proof
            .verify(&s1_acc, &s2_acc, &set! {1}, &pk)
            .unwrap();
        let union_proof = FinalProof::<Bls12_381>::new(Op::Union, &s1, &s2, &pk);
        union_proof
            .verify(&s1_acc, &s2_acc, &set! {1, 2, 3, 5}, &pk)
            .unwrap();
        let diff_proof = FinalProof::<Bls12_381>::new(Op::Difference, &s1, &s2, &pk);
        diff_proof
            .verify(&s1_acc, &s2_acc, &set! {2, 3}, &pk)
            .unwrap();
    }
}
