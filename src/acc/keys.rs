use super::utils::{FixedBaseCurvePow, FixedBaseScalarPow};
use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ff::UniformRand;
use core::marker::PhantomData;
use rand::{CryptoRng, RngCore};
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

/// Secret key of the accumulators.
pub struct AccSecretKeyWithPowCache<E: PairingEngine> {
    #[allow(dead_code)]
    pub(crate) s: E::Fr,
    #[allow(dead_code)]
    pub(crate) r: E::Fr,
    pub(crate) alpha: E::Fr,
    pub(crate) beta: E::Fr,
    pub(crate) gamma: E::Fr,
    pub(crate) delta: E::Fr,
    /// Used to compute g^x.
    pub(crate) g_pow: FixedBaseCurvePow<E::G1Projective>,
    /// Used to compute h^x.
    pub(crate) h_pow: FixedBaseCurvePow<E::G2Projective>,
    /// Used to compute s^x.
    pub(crate) s_pow: FixedBaseScalarPow<E::Fr>,
    /// Used to compute r^x.
    pub(crate) r_pow: FixedBaseScalarPow<E::Fr>,
    _marker: PhantomData<E>,
}

impl<E: PairingEngine> From<AccSecretKey<E>> for AccSecretKeyWithPowCache<E> {
    fn from(sk: AccSecretKey<E>) -> Self {
        let g = <E::G1Projective as ProjectiveCurve>::prime_subgroup_generator();
        let h = <E::G2Projective as ProjectiveCurve>::prime_subgroup_generator();

        Self {
            s: sk.s,
            r: sk.r,
            alpha: sk.alpha,
            beta: sk.beta,
            gamma: sk.gamma,
            delta: sk.delta,
            g_pow: FixedBaseCurvePow::build(&g),
            h_pow: FixedBaseCurvePow::build(&h),
            s_pow: FixedBaseScalarPow::build(&sk.s),
            r_pow: FixedBaseScalarPow::build(&sk.r),
            _marker: PhantomData,
        }
    }
}

/// Public key of the accumulators.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AccPublicKey<E: PairingEngine> {
    /// q
    pub(crate) q: u64,
    /// g
    #[serde(with = "super::serde_impl")]
    pub(crate) g: E::G1Affine,
    /// h
    #[serde(with = "super::serde_impl")]
    pub(crate) h: E::G2Affine,
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
    pub fn gen_key(sk: &AccSecretKeyWithPowCache<E>, q: u64) -> Self {
        let q_usize = q as usize;
        let q_fr = E::Fr::from(q);

        let g_alpha = sk.g_pow.apply(&sk.alpha).into_affine();
        let g_beta = sk.g_pow.apply(&sk.beta).into_affine();
        let g_gamma = sk.g_pow.apply(&sk.gamma).into_affine();
        let g_delta = sk.g_pow.apply(&sk.delta).into_affine();

        let g_s_q = sk.g_pow.apply(&sk.s_pow.apply(&q_fr)).into_affine();
        let h_r_q = sk.h_pow.apply(&sk.r_pow.apply(&q_fr)).into_affine();

        let mut g_s_i = Vec::with_capacity(q_usize - 1);
        (1..q_usize)
            .into_par_iter()
            .map(|i| {
                let s_i = sk.s_pow.apply(&E::Fr::from(i as u64));
                sk.g_pow.apply(&s_i).into_affine()
            })
            .collect_into_vec(&mut g_s_i);

        let mut g_alpha_s_i = Vec::with_capacity(q_usize - 1);
        (1..q_usize)
            .into_par_iter()
            .map(|i| {
                let s_i = sk.s_pow.apply(&E::Fr::from(i as u64));
                let alpha_s_i = sk.alpha * s_i;
                sk.g_pow.apply(&alpha_s_i).into_affine()
            })
            .collect_into_vec(&mut g_alpha_s_i);

        let mut h_r_i = Vec::with_capacity(q_usize - 1);
        (1..q_usize)
            .into_par_iter()
            .map(|i| {
                let r_i = sk.r_pow.apply(&E::Fr::from(i as u64));
                sk.h_pow.apply(&r_i).into_affine()
            })
            .collect_into_vec(&mut h_r_i);

        let mut h_beta_r_i = Vec::with_capacity(q_usize - 1);
        (1..q_usize)
            .into_par_iter()
            .map(|i| {
                let r_i = sk.r_pow.apply(&E::Fr::from(i as u64));
                let beta_r_i = sk.beta * r_i;
                sk.h_pow.apply(&beta_r_i).into_affine()
            })
            .collect_into_vec(&mut h_beta_r_i);

        let mut h_gamma_r_s_i = Vec::with_capacity(q_usize - 1);
        (1..q_usize)
            .into_par_iter()
            .map(|i| {
                let r_i = sk.r_pow.apply(&E::Fr::from(i as u64));
                let s_i = sk.s_pow.apply(&E::Fr::from(q - i as u64));
                let gamma_r_s_i = sk.gamma * r_i * s_i;
                sk.h_pow.apply(&gamma_r_s_i).into_affine()
            })
            .collect_into_vec(&mut h_gamma_r_s_i);

        // [2q-1] \ {q}
        let one_dim_indexes: Vec<u64> = (1..2 * q).filter(|&x| x != q).collect();
        // ([2q-1] \ {q}) \times ([2q-1] \ {q})
        let two_dim_indexes: Vec<(u64, u64)> = one_dim_indexes
            .iter()
            .flat_map(|i| one_dim_indexes.iter().map(move |j| (*i, *j)))
            .collect();

        let mut h_r_i_s_j = Vec::with_capacity((2 * q_usize - 2) * (2 * q_usize - 2));
        two_dim_indexes
            .par_iter()
            .map(|(i, j)| {
                let r_i = sk.r_pow.apply(&E::Fr::from(*i));
                let s_j = sk.s_pow.apply(&E::Fr::from(*j));
                let r_i_s_j = r_i * s_j;
                sk.h_pow.apply(&r_i_s_j).into_affine()
            })
            .collect_into_vec(&mut h_r_i_s_j);

        let mut h_delta_r_i_s_j = Vec::with_capacity((2 * q_usize - 2) * (2 * q_usize - 2));
        two_dim_indexes
            .par_iter()
            .map(|(i, j)| {
                let r_i = sk.r_pow.apply(&E::Fr::from(*i));
                let s_j = sk.s_pow.apply(&E::Fr::from(*j));
                let delta_r_i_s_j = sk.delta * r_i * s_j;
                sk.h_pow.apply(&delta_r_i_s_j).into_affine()
            })
            .collect_into_vec(&mut h_delta_r_i_s_j);

        Self {
            q,
            g: <E::G1Projective as ProjectiveCurve>::prime_subgroup_generator().into_affine(),
            h: <E::G2Projective as ProjectiveCurve>::prime_subgroup_generator().into_affine(),
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
            h_r_i_s_j,
            h_delta_r_i_s_j,
            _marker: PhantomData,
        }
    }

    /// Return g
    pub(crate) fn get_g(&self) -> E::G1Affine {
        self.g
    }

    /// Return h
    pub(crate) fn get_h(&self) -> E::G2Affine {
        self.h
    }

    /// Return g^{s^i} i \in [q-1]
    pub(crate) fn get_g_s_i(&self, i: u64) -> Option<E::G1Affine> {
        self.g_s_i.get(map_i_to_index(i, self.q)).copied()
    }

    /// Return g^{\alpha \cdot s^i} i \in [q-1]
    pub(crate) fn get_g_alpha_s_i(&self, i: u64) -> Option<E::G1Affine> {
        self.g_alpha_s_i.get(map_i_to_index(i, self.q)).copied()
    }

    /// Return h^{r^i} i \in [q-1]
    pub(crate) fn get_h_r_i(&self, i: u64) -> Option<E::G2Affine> {
        self.h_r_i.get(map_i_to_index(i, self.q)).copied()
    }

    /// Return h^{\beta \cdot r^i} i \in [q-1]
    pub(crate) fn get_h_beta_r_i(&self, i: u64) -> Option<E::G2Affine> {
        self.h_beta_r_i.get(map_i_to_index(i, self.q)).copied()
    }

    /// Return h^{\gamma \cdot r^i \cdot s^{q-i}} i \in [q-1]
    pub(crate) fn get_h_gamma_r_s_i(&self, i: u64) -> Option<E::G2Affine> {
        self.h_gamma_r_s_i.get(map_i_to_index(i, self.q)).copied()
    }

    /// Return h^{r^i \cdot s^j} (i, j) \in ([2q-1] \ {q}) \times ([2q-1] \ {q})
    pub(crate) fn get_h_r_i_s_j(&self, i: u64, j: u64) -> Option<E::G2Affine> {
        if i == self.q || j == self.q {
            return None;
        }
        self.h_r_i_s_j.get(map_i_j_to_index(i, j, self.q)).copied()
    }

    /// Return h^{\delta r^i \cdot s^j} (i, j) \in ([2q-1] \ {q}) \times ([2q-1] \ {q})
    pub(crate) fn get_h_delta_r_i_s_j(&self, i: u64, j: u64) -> Option<E::G2Affine> {
        if i == self.q || j == self.q {
            return None;
        }
        self.h_delta_r_i_s_j
            .get(map_i_j_to_index(i, j, self.q))
            .copied()
    }
}

/// Map i \in [q-1] -> 0..q - 2
#[inline(always)]
fn map_i_to_index(i: u64, q: u64) -> usize {
    debug_assert!(i >= 1 && i < q);
    (i - 1) as usize
}

/// Map (i, j) \in ([2q-1] \ {q}) \times ([2q-1] \ {q}) -> 0..(2q-2)*(2q-2)
#[inline(always)]
fn map_i_j_to_index(i: u64, j: u64, q: u64) -> usize {
    debug_assert!(i >= 1 && i != q && i < 2 * q);
    debug_assert!(j >= 1 && j != q && j < 2 * q);
    let _i = if i > q { i - 2 } else { i - 1 };
    let _j = if j > q { j - 2 } else { j - 1 };
    (_i * (2 * q - 2) + _j) as usize
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Bls12_381;
    use ark_ec::AffineCurve;
    use ark_ff::{Field, PrimeField};

    #[test]
    fn test_key_gen() {
        let mut rng = rand::thread_rng();
        let q = 5;
        let sk = AccSecretKey::<Bls12_381>::rand(&mut rng).into();
        let pk = AccPublicKey::<Bls12_381>::gen_key(&sk, q);

        let g = pk.get_g();
        let h = pk.get_h();
        let q_fr = <Bls12_381 as PairingEngine>::Fr::from(q);

        for i in 1..=(q - 1) {
            let i_fr = <Bls12_381 as PairingEngine>::Fr::from(i);
            let s_i = sk.s.pow(i_fr.into_repr());
            let r_i = sk.r.pow(i_fr.into_repr());
            let s_q_i = sk.s.pow((q_fr - i_fr).into_repr());
            assert_eq!(pk.get_g_s_i(i), Some(g.mul(s_i).into_affine()));
            assert_eq!(
                pk.get_g_alpha_s_i(i),
                Some(g.mul(sk.alpha * s_i).into_affine())
            );
            assert_eq!(pk.get_h_r_i(i), Some(h.mul(r_i).into_affine()));
            assert_eq!(
                pk.get_h_beta_r_i(i),
                Some(h.mul(sk.beta * r_i).into_affine())
            );
            assert_eq!(
                pk.get_h_gamma_r_s_i(i),
                Some(h.mul(sk.gamma * r_i * s_q_i).into_affine())
            );
        }

        for i in 1..=(2 * q - 1) {
            for j in 1..=(2 * q - 1) {
                if i == q || j == q {
                    assert!(pk.get_h_r_i_s_j(i, j).is_none());
                    assert!(pk.get_h_delta_r_i_s_j(i, j).is_none());
                } else {
                    let i_fr = <Bls12_381 as PairingEngine>::Fr::from(i);
                    let j_fr = <Bls12_381 as PairingEngine>::Fr::from(j);
                    let r_i = sk.r.pow(i_fr.into_repr());
                    let s_j = sk.s.pow(j_fr.into_repr());
                    assert_eq!(pk.get_h_r_i_s_j(i, j), Some(h.mul(r_i * s_j).into_affine()));
                    assert_eq!(
                        pk.get_h_delta_r_i_s_j(i, j),
                        Some(h.mul(sk.delta * r_i * s_j).into_affine())
                    );
                }
            }
        }
    }
}
