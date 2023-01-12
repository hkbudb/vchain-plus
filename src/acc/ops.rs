use super::{
    acc_value::{cal_acc_pk, AccValue},
    keys::AccPublicKey,
    poly::{poly_a, poly_b, poly_variable_minus_one, Poly, Variable, R, S},
    set::Set,
};
use anyhow::{ensure, Context as _, Result};
use ark_ec::{msm::VariableBaseMSM, PairingEngine, ProjectiveCurve};
use ark_ff::{PrimeField, Zero};
use core::marker::PhantomData;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Copy, Clone)]
struct SendPtr<T>(*mut T);
unsafe impl<T> Send for SendPtr<T> {}

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
    #[serde(bound = "E: PairingEngine")]
    _marker: PhantomData<E>,
}

impl<E: PairingEngine> IntersectionProof<E> {
    #[allow(clippy::many_single_char_names)]
    #[allow(clippy::too_many_arguments)]
    fn new(
        set: &Set,
        q_poly: &Poly<E::Fr>,
        x: Variable,
        y: Variable,
        g: E::G1Affine,
        get_g_x_i: impl Fn(u64) -> E::G1Affine + Sync + Send,
        get_g_beta_x_i: impl Fn(u64) -> E::G1Affine + Sync + Send,
        get_g_x_i_y_j: impl Fn(u64, u64) -> E::G1Affine + Sync + Send,
        get_g_delta_x_i_y_j: impl Fn(u64, u64) -> E::G1Affine + Sync + Send,
    ) -> Self {
        let (g_x, g_x_beta) = rayon::join(
            || cal_acc_pk(set, &get_g_x_i),
            || cal_acc_pk(set, &get_g_beta_x_i),
        );
        let l_x = cal_acc_pk(set, |i| if i == 1 { g } else { get_g_x_i(i - 1) });

        let q_poly_num_terms = q_poly.num_terms();
        let mut bases: Vec<E::G1Affine> = Vec::with_capacity(q_poly_num_terms);
        let mut delta_bases: Vec<E::G1Affine> = Vec::with_capacity(q_poly_num_terms);
        let mut scalars: Vec<<E::Fr as PrimeField>::BigInt> = Vec::with_capacity(q_poly_num_terms);

        let bases_ptr = bases.as_mut_ptr();
        let delta_bases_ptr = delta_bases.as_mut_ptr();
        let scalars_ptr = scalars.as_mut_ptr();

        q_poly.coeff_par_iter_with_index().for_each_with(
            (
                SendPtr(bases_ptr),
                SendPtr(delta_bases_ptr),
                SendPtr(scalars_ptr),
            ),
            |(bases_ptr, delta_bases_ptr, scalars_ptr), (idx, (term, coeff))| {
                let i = term.get_power(x);
                let j = term.get_power(y);
                unsafe {
                    *bases_ptr.0.add(idx) = get_g_x_i_y_j(i, j);
                    *delta_bases_ptr.0.add(idx) = get_g_delta_x_i_y_j(i, j);
                    *scalars_ptr.0.add(idx) = coeff.into_repr();
                }
            },
        );

        unsafe {
            bases.set_len(q_poly_num_terms);
            delta_bases.set_len(q_poly_num_terms);
            scalars.set_len(q_poly_num_terms);
        }

        let (q_x_y, q_x_y_delta) = rayon::join(
            || VariableBaseMSM::multi_scalar_mul(&bases[..], &scalars[..]).into_affine(),
            || VariableBaseMSM::multi_scalar_mul(&delta_bases[..], &scalars[..]).into_affine(),
        );

        Self {
            g_x,
            g_x_beta,
            q_x_y,
            q_x_y_delta,
            l_x,
            _marker: PhantomData,
        }
    }

    #[allow(clippy::too_many_arguments)]
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
            "e(A, B) != e(I, h^{{y^q}}) * e(Q_{{x,y}}, h)"
        );
        ensure!(
            E::pairing(self.g_x, h_beta) == E::pairing(self.g_x_beta, h),
            "e(I, h^{{beta}}) != e(I_{{beta}}, h)"
        );
        ensure!(
            E::pairing(self.q_x_y, h_delta) == E::pairing(self.q_x_y_delta, h),
            "e(Q_{{x,y}}, h^{{delta}}) != e(Q_{{x,y,delta}}, h)"
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
    #[serde(bound = "E: PairingEngine")]
    inner_proof_r: IntersectionProof<E>,
    #[serde(bound = "E: PairingEngine")]
    inner_proof_s: IntersectionProof<E>,
    #[serde(with = "super::serde_impl")]
    result_acc_s_r_gamma: E::G1Affine,
    #[serde(with = "super::serde_impl")]
    result_acc_r_s_gamma: E::G1Affine,
    #[serde(with = "super::serde_impl")]
    z_s_r: E::G1Affine,
    #[serde(with = "super::serde_impl")]
    z_r_s: E::G1Affine,
}

impl<E: PairingEngine> IntermediateProof<E> {
    pub fn verify(
        &self,
        lhs_acc: &AccValue<E>,
        rhs_acc: &AccValue<E>,
        result_acc: &AccValue<E>,
        pk: &AccPublicKey<E>,
    ) -> Result<()> {
        let (verify_inner_proof_r, verify_inner_proof_s) = rayon::join(
            || {
                self.inner_proof_r.verify(
                    lhs_acc.g_s,
                    rhs_acc.h_r_s,
                    pk.h,
                    pk.h_s_q,
                    pk.h_beta,
                    pk.h_delta,
                    pk.h_r,
                )
            },
            || {
                self.inner_proof_s.verify(
                    lhs_acc.g_r,
                    rhs_acc.h_s_r,
                    pk.h,
                    pk.h_r_q,
                    pk.h_beta,
                    pk.h_delta,
                    pk.h_s,
                )
            },
        );

        verify_inner_proof_r.context("failed to verify the inner_proof_r.")?;
        verify_inner_proof_s.context("failed to verify the inner_proof_s.")?;

        match self.op {
            Op::Intersection => {
                ensure!(
                    result_acc.g_s == self.inner_proof_s.g_x,
                    "acc(set).g_s is invalid."
                );
                ensure!(
                    result_acc.g_r == self.inner_proof_r.g_x,
                    "acc(set).g_r is invalid."
                );
            }
            Op::Union => {
                ensure!(
                    result_acc.g_s == lhs_acc.g_s + rhs_acc.g_s + (-self.inner_proof_s.g_x),
                    "acc(set).g_s is invalid."
                );
                ensure!(
                    result_acc.g_r == lhs_acc.g_r + rhs_acc.g_r + (-self.inner_proof_r.g_x),
                    "acc(set).g_r is invalid."
                );
            }
            Op::Difference => {
                ensure!(
                    result_acc.g_s == lhs_acc.g_s + (-self.inner_proof_s.g_x),
                    "acc(set).g_s is invalid."
                );
                ensure!(
                    result_acc.g_r == lhs_acc.g_r + (-self.inner_proof_r.g_x),
                    "acc(set).g_r is invalid."
                );
            }
        }

        ensure!(
            E::pairing(pk.g_gamma, result_acc.h_r_s) == E::pairing(self.result_acc_r_s_gamma, pk.h),
            "e(g^{{gamma}}, R_{{r,s}}) != e(R_{{r,s,gamma}}, h)"
        );
        ensure!(
            E::pairing(pk.g_gamma, result_acc.h_s_r) == E::pairing(self.result_acc_s_r_gamma, pk.h),
            "e(g^{{gamma}}, R_{{s,r}}) != e(R_{{s,r,gamma}}, h)"
        );

        ensure!(
            E::product_of_pairings(&[
                (result_acc.g_r.into(), pk.h.into()),
                (pk.g.into(), (-result_acc.h_r_s).into())
            ]) == E::pairing(self.z_s_r, pk.h_s + (-pk.h)),
            "e(R_{{r}}, h) * e(g, 1/R_{{r,s}}) != e(Z_{{s,r}}, h^{{s-1}})"
        );
        ensure!(
            E::product_of_pairings(&[
                (result_acc.g_s.into(), pk.h.into()),
                (pk.g.into(), (-result_acc.h_s_r).into())
            ]) == E::pairing(self.z_r_s, pk.h_r + (-pk.h)),
            "e(R_{{s}}, h) * e(g, 1/R_{{s,r}}) != e(Z_{{r,s}}, h^{{r-1}})"
        );

        Ok(())
    }
}

pub fn compute_set_operation_intermediate<E: PairingEngine>(
    op: Op,
    lhs_set: &Set,
    lhs_acc: &AccValue<E>,
    rhs_set: &Set,
    rhs_acc: &AccValue<E>,
    pk: &AccPublicKey<E>,
) -> (Set, AccValue<E>, IntermediateProof<E>) {
    let intersection_set = lhs_set & rhs_set;
    let lhs_poly: Poly<E::Fr> = poly_a(lhs_set, S);
    let rhs_poly: Poly<E::Fr> = poly_b(rhs_set, R, S, pk.q);
    let mut q_poly = &lhs_poly * &rhs_poly;
    q_poly.remove_intersected_term(S, pk.q, &intersection_set);
    let (inner_proof_r, inner_proof_s) = rayon::join(
        || {
            IntersectionProof::<E>::new(
                &intersection_set,
                &q_poly,
                R,
                S,
                pk.g,
                |i| pk.get_g_r_i(i),
                |i| pk.get_g_beta_r_i(i),
                |i, j| pk.get_g_r_i_s_j(i, j),
                |i, j| pk.get_g_delta_r_i_s_j(i, j),
            )
        },
        || {
            IntersectionProof::<E>::new(
                &intersection_set,
                &q_poly,
                S,
                R,
                pk.g,
                |i| pk.get_g_s_i(i),
                |i| pk.get_g_beta_s_i(i),
                |i, j| pk.get_g_r_i_s_j(i, j),
                |i, j| pk.get_g_delta_r_i_s_j(i, j),
            )
        },
    );

    let result_set = match op {
        Op::Intersection => intersection_set,
        Op::Union => lhs_set | rhs_set,
        Op::Difference => lhs_set / &intersection_set,
    };
    let result_acc = match op {
        Op::Intersection => AccValue::<E>::new(
            inner_proof_s.g_x,
            inner_proof_r.g_x,
            cal_acc_pk(&result_set, |i| pk.get_h_s_r_i(i)),
            cal_acc_pk(&result_set, |i| pk.get_h_r_s_i(i)),
        ),
        Op::Union => AccValue::<E>::new(
            lhs_acc.g_s + rhs_acc.g_s + (-inner_proof_s.g_x),
            lhs_acc.g_r + rhs_acc.g_r + (-inner_proof_r.g_x),
            cal_acc_pk(&result_set, |i| pk.get_h_s_r_i(i)),
            cal_acc_pk(&result_set, |i| pk.get_h_r_s_i(i)),
        ),
        Op::Difference => AccValue::<E>::new(
            lhs_acc.g_s + (-inner_proof_s.g_x),
            lhs_acc.g_r + (-inner_proof_r.g_x),
            cal_acc_pk(&result_set, |i| pk.get_h_s_r_i(i)),
            cal_acc_pk(&result_set, |i| pk.get_h_r_s_i(i)),
        ),
    };
    let (result_acc_s_r_gamma, result_acc_r_s_gamma) = rayon::join(
        || cal_acc_pk(&result_set, |i| pk.get_g_gamma_s_r_i(i)),
        || cal_acc_pk(&result_set, |i| pk.get_g_gamma_r_s_i(i)),
    );

    let result_y_poly = poly_a::<E::Fr>(&result_set, R);
    let result_x_y_poly = poly_b::<E::Fr>(&result_set, R, S, pk.q);
    let (z_poly, r_poly) = (result_y_poly - result_x_y_poly) / &poly_variable_minus_one::<E::Fr>(S);
    debug_assert!(r_poly.is_zero());

    let z_poly_num_terms = z_poly.num_terms();
    let mut z_s_r_bases: Vec<E::G1Affine> = Vec::with_capacity(z_poly_num_terms);
    let mut z_r_s_bases: Vec<E::G1Affine> = Vec::with_capacity(z_poly_num_terms);
    let mut scalars: Vec<<E::Fr as PrimeField>::BigInt> = Vec::with_capacity(z_poly_num_terms);

    let z_s_r_bases_ptr = z_s_r_bases.as_mut_ptr();
    let z_r_s_bases_ptr = z_r_s_bases.as_mut_ptr();
    let scalars_ptr = scalars.as_mut_ptr();

    z_poly.coeff_par_iter_with_index().for_each_with(
        (
            SendPtr(z_s_r_bases_ptr),
            SendPtr(z_r_s_bases_ptr),
            SendPtr(scalars_ptr),
        ),
        |(z_s_r_bases_ptr, z_r_s_bases_ptr, scalars_ptr), (idx, (term, coeff))| {
            let i = term.get_power(R);
            let j = term.get_power(S);
            let (z_s_r_base, z_r_s_base) = match (i, j) {
                (0, 0) => (pk.g, pk.g),
                (0, _) => (pk.get_g_s_i(j), pk.get_g_r_i(j)),
                (_, 0) => (pk.get_g_r_i(i), pk.get_g_s_i(i)),
                (_, _) => (pk.get_g_r_i_s_j(i, j), pk.get_g_r_i_s_j(j, i)),
            };
            unsafe {
                *z_s_r_bases_ptr.0.add(idx) = z_s_r_base;
                *z_r_s_bases_ptr.0.add(idx) = z_r_s_base;
                *scalars_ptr.0.add(idx) = coeff.into_repr();
            }
        },
    );

    unsafe {
        z_s_r_bases.set_len(z_poly_num_terms);
        z_r_s_bases.set_len(z_poly_num_terms);
        scalars.set_len(z_poly_num_terms);
    }

    let (z_s_r, z_r_s) = rayon::join(
        || VariableBaseMSM::multi_scalar_mul(&z_s_r_bases[..], &scalars[..]).into_affine(),
        || VariableBaseMSM::multi_scalar_mul(&z_r_s_bases[..], &scalars[..]).into_affine(),
    );

    let proof = IntermediateProof {
        op,
        inner_proof_r,
        inner_proof_s,
        result_acc_s_r_gamma,
        result_acc_r_s_gamma,
        z_s_r,
        z_r_s,
    };

    (result_set, result_acc, proof)
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FinalProof<E: PairingEngine> {
    op: Op,
    #[serde(bound = "E: PairingEngine")]
    inner_proof: IntersectionProof<E>,
}

impl<E: PairingEngine> FinalProof<E> {
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

pub fn compute_set_operation_final<E: PairingEngine>(
    op: Op,
    lhs_set: &Set,
    rhs_set: &Set,
    pk: &AccPublicKey<E>,
) -> (Set, FinalProof<E>) {
    let intersection_set = lhs_set & rhs_set;
    let lhs_poly: Poly<E::Fr> = poly_a(lhs_set, S);
    let rhs_poly: Poly<E::Fr> = poly_b(rhs_set, R, S, pk.q);
    let mut q_poly = &lhs_poly * &rhs_poly;
    q_poly.remove_intersected_term(S, pk.q, &intersection_set);
    let inner_proof = IntersectionProof::new(
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
    let proof = FinalProof { op, inner_proof };
    let result = match op {
        Op::Intersection => intersection_set,
        Op::Union => lhs_set | rhs_set,
        Op::Difference => lhs_set / &intersection_set,
    };
    (result, proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{acc::keys::AccSecretKey, set};
    use ark_bn254::{Bn254, Fr};

    #[test]
    fn test_intersection_proof() {
        let mut rng = rand::thread_rng();
        let q = 10;
        let sk = AccSecretKey::<Bn254>::rand(&mut rng).into();
        let pk = AccPublicKey::<Bn254>::gen_key(&sk, q);

        let s1 = set! {1, 2, 3};
        let s2 = set! {1, 5};
        let s3 = set! {1};

        let s1_a_poly: Poly<Fr> = poly_a(&s1, S);
        let s2_b_poly: Poly<Fr> = poly_b(&s2, R, S, q);
        let mut q_poly = &s1_a_poly * &s2_b_poly;
        q_poly.remove_intersected_term(S, pk.q, &s3);

        let s1_acc = AccValue::from_set_sk(&s1, &sk, q);
        let s2_acc = AccValue::from_set_sk(&s2, &sk, q);

        let proof = IntersectionProof::<Bn254>::new(
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

        let bin = bincode::serialize(&proof).unwrap();
        assert_eq!(
            bincode::deserialize::<IntersectionProof<_>>(&bin[..]).unwrap(),
            proof
        );
    }

    #[test]
    fn test_intermediate_proof() {
        let mut rng = rand::thread_rng();
        let q = 10;
        let sk = AccSecretKey::<Bn254>::rand(&mut rng).into();
        let pk = AccPublicKey::<Bn254>::gen_key(&sk, q);

        let s1 = set! {1, 2, 3};
        let s2 = set! {1, 5};

        let s1_acc = AccValue::from_set_sk(&s1, &sk, q);
        let s2_acc = AccValue::from_set_sk(&s2, &sk, q);
        let intersection_acc = AccValue::from_set_sk(&set! {1}, &sk, q);
        let union_acc = AccValue::from_set_sk(&set! {1, 2, 3, 5}, &sk, q);
        let _difference_acc = AccValue::from_set_sk(&set! {2, 3}, &sk, q);

        let (intersection_result_set, intersection_result_acc, intersection_proof) =
            compute_set_operation_intermediate::<Bn254>(
                Op::Intersection,
                &s1,
                &s1_acc,
                &s2,
                &s2_acc,
                &pk,
            );
        assert_eq!(intersection_result_set, set! {1});
        assert_eq!(intersection_result_acc, intersection_acc);
        intersection_proof
            .verify(&s1_acc, &s2_acc, &intersection_result_acc, &pk)
            .unwrap();

        let bin = bincode::serialize(&intersection_proof).unwrap();
        assert_eq!(
            bincode::deserialize::<IntermediateProof<_>>(&bin[..]).unwrap(),
            intersection_proof
        );

        let (union_result_set, union_result_acc, union_proof) =
            compute_set_operation_intermediate::<Bn254>(Op::Union, &s1, &s1_acc, &s2, &s2_acc, &pk);
        assert_eq!(union_result_set, set! {1, 2, 3, 5});
        assert_eq!(union_result_acc, union_acc);
        union_proof
            .verify(&s1_acc, &s2_acc, &union_result_acc, &pk)
            .unwrap();

        let bin = bincode::serialize(&union_proof).unwrap();
        assert_eq!(
            bincode::deserialize::<IntermediateProof<_>>(&bin[..]).unwrap(),
            union_proof
        );

        let (diff_result_set, diff_result_acc, diff_proof) =
            compute_set_operation_intermediate::<Bn254>(
                Op::Difference,
                &s1,
                &s1_acc,
                &s2,
                &s2_acc,
                &pk,
            );
        assert_eq!(diff_result_set, set! {2, 3});
        assert_eq!(diff_result_acc, diff_result_acc);
        diff_proof
            .verify(&s1_acc, &s2_acc, &diff_result_acc, &pk)
            .unwrap();

        let bin = bincode::serialize(&diff_proof).unwrap();
        assert_eq!(
            bincode::deserialize::<IntermediateProof<_>>(&bin[..]).unwrap(),
            diff_proof
        );
    }

    #[test]
    fn test_final_proof() {
        let mut rng = rand::thread_rng();
        let q = 10;
        let sk = AccSecretKey::<Bn254>::rand(&mut rng).into();
        let pk = AccPublicKey::<Bn254>::gen_key(&sk, q);

        let s1 = set! {1, 2, 3};
        let s2 = set! {1, 5};

        let s1_acc = AccValue::from_set_sk(&s1, &sk, q);
        let s2_acc = AccValue::from_set_sk(&s2, &sk, q);

        let (intersection_result, intersection_proof) =
            compute_set_operation_final::<Bn254>(Op::Intersection, &s1, &s2, &pk);
        assert_eq!(intersection_result, set! {1});
        intersection_proof
            .verify(&s1_acc, &s2_acc, &intersection_result, &pk)
            .unwrap();

        let bin = bincode::serialize(&intersection_proof).unwrap();
        assert_eq!(
            bincode::deserialize::<FinalProof<_>>(&bin[..]).unwrap(),
            intersection_proof
        );

        let (union_result, union_proof) =
            compute_set_operation_final::<Bn254>(Op::Union, &s1, &s2, &pk);
        assert_eq!(union_result, set! {1, 2, 3, 5});
        union_proof
            .verify(&s1_acc, &s2_acc, &union_result, &pk)
            .unwrap();

        let bin = bincode::serialize(&union_proof).unwrap();
        assert_eq!(
            bincode::deserialize::<FinalProof<_>>(&bin[..]).unwrap(),
            union_proof
        );

        let (diff_result, diff_proof) =
            compute_set_operation_final::<Bn254>(Op::Difference, &s1, &s2, &pk);
        assert_eq!(diff_result, set! {2, 3});
        diff_proof
            .verify(&s1_acc, &s2_acc, &diff_result, &pk)
            .unwrap();

        let bin = bincode::serialize(&diff_proof).unwrap();
        assert_eq!(
            bincode::deserialize::<FinalProof<_>>(&bin[..]).unwrap(),
            diff_proof
        );
    }
}
