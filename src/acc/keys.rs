use super::utils::{FixedBaseCurvePow, FixedBaseScalarPow};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{PrimeField, UniformRand};
use core::{marker::PhantomData, ops::Mul};
use rand_core::{CryptoRng, RngCore};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

/// Secret key of the accumulators.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AccSecretKey<E: PairingEngine> {
    #[serde(with = "super::serde_impl")]
    pub(crate) s: E::Fr,
    #[serde(with = "super::serde_impl")]
    pub(crate) r: E::Fr,
    #[serde(with = "super::serde_impl")]
    pub(crate) alpha: E::Fr,
    #[serde(with = "super::serde_impl")]
    pub(crate) beta: E::Fr,
    #[serde(with = "super::serde_impl")]
    pub(crate) gamma: E::Fr,
    #[serde(with = "super::serde_impl")]
    pub(crate) delta: E::Fr,
    _marker: PhantomData<E>,
}

impl<E: PairingEngine> AccSecretKey<E> {
    pub fn rand(mut rng: impl RngCore + CryptoRng) -> Self {
        Self {
            s: E::Fr::rand(&mut rng),
            r: E::Fr::rand(&mut rng),
            alpha: E::Fr::rand(&mut rng),
            beta: E::Fr::rand(&mut rng),
            gamma: E::Fr::rand(&mut rng),
            delta: E::Fr::rand(&mut rng),
            _marker: PhantomData,
        }
    }
}

/// Public key of the accumulators.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AccPublicKey<E: PairingEngine> {
    pub(crate) q: u64,
    /// g^\alpha
    #[serde(with = "super::serde_impl")]
    pub(crate) g_alpha: E::G1Affine,
    /// g^\beta
    #[serde(with = "super::serde_impl")]
    pub(crate) g_beta: E::G1Affine,
    /// g^\gamma
    #[serde(with = "super::serde_impl")]
    pub(crate) g_gamma: E::G1Affine,
    /// g^\delta
    #[serde(with = "super::serde_impl")]
    pub(crate) g_delta: E::G1Affine,
    /// g^{s^q}
    #[serde(with = "super::serde_impl")]
    pub(crate) g_s_q: E::G1Affine,
    /// h^{r^q}
    #[serde(with = "super::serde_impl")]
    pub(crate) h_r_q: E::G2Affine,
    /// g^{s^i} i \in [q-1]
    #[serde(with = "super::serde_impl")]
    pub(crate) g_s_i: Vec<E::G1Affine>,
    /// g^{\alpha \cdot s^i} i \in [q-1]
    #[serde(with = "super::serde_impl")]
    pub(crate) g_alpha_s_i: Vec<E::G1Affine>,
    /// h^{r^i} i \in [q-1]
    #[serde(with = "super::serde_impl")]
    pub(crate) h_r_i: Vec<E::G2Affine>,
    /// h^{\beta \cdot r^i} i \in [q-1]
    #[serde(with = "super::serde_impl")]
    pub(crate) h_beta_r_i: Vec<E::G2Affine>,
    /// h^{\gamma \cdot r^i \cdot s^{q-i}} i \in [q-1]
    #[serde(with = "super::serde_impl")]
    pub(crate) h_gamma_r_s_i: Vec<E::G2Affine>,
    /// h^{r^i \cdot s^j} (i, j) \in ([2q-1] \ {q}) \times ([2q-1] \ {q})
    #[serde(with = "super::serde_impl")]
    pub(crate) h_r_i_s_j: Vec<E::G2Affine>,
    /// h^{\delta r^i \cdot s^j} (i, j) \in ([2q-1] \ {q}) \times ([2q-1] \ {q})
    #[serde(with = "super::serde_impl")]
    pub(crate) h_delta_r_i_s_j: Vec<E::G2Affine>,
    _marker: PhantomData<E>,
}

impl<E: PairingEngine> AccPublicKey<E> {
    pub fn gen_key(sk: &AccSecretKey<E>, q: u64) -> Self {
        let q_usize = q as usize;
        let q_fr = E::Fr::from(q);

        let g = <E::G1Projective as ProjectiveCurve>::prime_subgroup_generator();
        let h = <E::G2Projective as ProjectiveCurve>::prime_subgroup_generator();

        let g_pow = FixedBaseCurvePow::build(&g);
        let h_pow = FixedBaseCurvePow::build(&h);
        let s_pow = FixedBaseScalarPow::build(&sk.s);
        let r_pow = FixedBaseScalarPow::build(&sk.r);

        let g_alpha = g_pow.apply(&sk.alpha).into_affine();
        let g_beta = g_pow.apply(&sk.beta).into_affine();
        let g_gamma = g_pow.apply(&sk.gamma).into_affine();
        let g_delta = g_pow.apply(&sk.delta).into_affine();

        let g_s_q = g_pow.apply(&s_pow.apply(&q_fr)).into_affine();
        let h_r_q = h_pow.apply(&r_pow.apply(&q_fr)).into_affine();

        let mut g_s_i = Vec::with_capacity(q_usize - 1);
        (1..q_usize)
            .into_par_iter()
            .map(|i| {
                let s_i = s_pow.apply(&E::Fr::from(i as u64));
                g_pow.apply(&s_i).into_affine()
            })
            .collect_into_vec(&mut g_s_i);

        let mut g_alpha_s_i = Vec::with_capacity(q_usize - 1);
        (1..q_usize)
            .into_par_iter()
            .map(|i| {
                let s_i = s_pow.apply(&E::Fr::from(i as u64));
                let alpha_s_i = sk.alpha * s_i;
                g_pow.apply(&alpha_s_i).into_affine()
            })
            .collect_into_vec(&mut g_alpha_s_i);

        let mut h_r_i = Vec::with_capacity(q_usize - 1);
        (1..q_usize)
            .into_par_iter()
            .map(|i| {
                let r_i = r_pow.apply(&E::Fr::from(i as u64));
                h_pow.apply(&r_i).into_affine()
            })
            .collect_into_vec(&mut h_r_i);

        let mut h_beta_r_i = Vec::with_capacity(q_usize - 1);
        (1..q_usize)
            .into_par_iter()
            .map(|i| {
                let r_i = r_pow.apply(&E::Fr::from(i as u64));
                let beta_r_i = sk.beta * r_i;
                h_pow.apply(&beta_r_i).into_affine()
            })
            .collect_into_vec(&mut h_beta_r_i);

        let mut h_gamma_r_s_i = Vec::with_capacity(q_usize - 1);
        (1..q_usize)
            .into_par_iter()
            .map(|i| {
                let r_i = r_pow.apply(&E::Fr::from(i as u64));
                let s_i = s_pow.apply(&E::Fr::from(q - i as u64));
                let gamma_r_s_i = sk.gamma * r_i * s_i;
                h_pow.apply(&gamma_r_s_i).into_affine()
            })
            .collect_into_vec(&mut h_gamma_r_s_i);

        Self {
            q,
            g_alpha,
            g_beta,
            g_gamma,
            g_delta,
            g_s_q,
            h_r_q,
            g_s_i,
            g_alpha_s_i,
            h_r_i,
            h_beta_r_i,
            h_gamma_r_s_i,
            h_r_i_s_j: Vec::new(),
            h_delta_r_i_s_j: Vec::new(),
            _marker: PhantomData,
        }
    }

    /// Return g^{s^i} i \in [q-1]
    pub(crate) fn get_g_s_i(&self, i: u64) -> Option<E::G1Affine> {
        self.g_s_i.get(i as usize - 1).copied()
    }

    /// Return g^{\alpha \cdot s^i} i \in [q-1]
    pub(crate) fn get_g_alpha_s_i(&self, i: u64) -> Option<E::G1Affine> {
        self.g_alpha_s_i.get(i as usize - 1).copied()
    }

    /// Return h^{r^i} i \in [q-1]
    pub(crate) fn get_h_r_i(&self, i: u64) -> Option<E::G2Affine> {
        self.h_r_i.get(i as usize - 1).copied()
    }

    /// Return h^{\beta \cdot r^i} i \in [q-1]
    pub(crate) fn get_h_beta_r_i(&self, i: u64) -> Option<E::G2Affine> {
        self.h_beta_r_i.get(i as usize - 1).copied()
    }

    /// Return h^{\gamma \cdot r^i \cdot s^{q-i}} i \in [q-1]
    pub(crate) fn get_h_gamma_r_s_i(&self, i: u64) -> Option<E::G2Affine> {
        self.h_gamma_r_s_i.get(i as usize - 1).copied()
    }

    /// Return h^{r^i \cdot s^j} (i, j) \in ([2q-1] \ {q}) \times ([2q-1] \ {q})
    pub(crate) fn get_h_r_i_s_j(&self, i: u64, j: u64) -> Option<E::G2Affine> {
        todo!()
    }

    /// Return h^{\delta r^i \cdot s^j} (i, j) \in ([2q-1] \ {q}) \times ([2q-1] \ {q})
    pub(crate) fn get_h_delta_r_i_s_j(&self, i: u64, j: u64) -> Option<E::G2Affine> {
        todo!()
    }
}

/// Map (i, j) \in ([2q-1] \ {q}) \times ([2q-1] \ {q}) -> [(2q-2)*(2q-2)]
#[inline]
fn map_i_j_to_index(i: u64, j: u64, q: u64) -> usize {
    debug_assert!(i >= 1 && i != q && i <= 2*q - 1);
    debug_assert!(j >= 1 && j != q && j <= 2*q - 1);
    todo!();
}
