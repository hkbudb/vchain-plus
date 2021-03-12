use super::{
    keys::{AccPublicKey, AccSecretKeyWithPowCache},
    set::Set,
};
use crate::digest::{Digest, Digestible};
use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ff::Zero;
use core::{
    marker::PhantomData,
    ops::{Add, Sub},
};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

#[inline]
fn cal_acc_g_pk<E, F>(set: &Set, f: F) -> E::G1Affine
where
    E: PairingEngine,
    F: Fn(u64) -> E::G1Affine + Sync,
{
    set.par_iter()
        .map(|i| f(i.get()))
        .fold(E::G1Projective::zero, |a, b| a.add_mixed(&b))
        .reduce(E::G1Projective::zero, |a, b| a + b)
        .into_affine()
}

#[inline]
fn cal_acc_h_pk<E, F>(set: &Set, f: F) -> E::G2Affine
where
    E: PairingEngine,
    F: Fn(u64) -> E::G2Affine + Sync,
{
    set.par_iter()
        .map(|i| f(i.get()))
        .fold(E::G2Projective::zero, |a, b| a.add_mixed(&b))
        .reduce(E::G2Projective::zero, |a, b| a + b)
        .into_affine()
}

#[inline]
fn cal_acc_sk<E, F>(set: &Set, f: F) -> E::Fr
where
    E: PairingEngine,
    F: Fn(u64) -> E::Fr + Sync,
{
    set.par_iter()
        .map(|i| f(i.get()))
        .reduce(E::Fr::zero, |a, b| a + b)
}

/// An accumulative value consists of both [`LeftAccValue`] and [`RightAccValue`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AccValue<E: PairingEngine> {
    /// g^{\sum s^i}
    pub(crate) g_s: E::G1Affine,
    /// g^{\sum r^i}
    pub(crate) g_r: E::G1Affine,
    /// h^{\sum s^i \cdot r^{q - i}}
    pub(crate) h_s_r: E::G2Affine,
    /// h^{\sum r^i \cdot s^{q - i}}
    pub(crate) h_r_s: E::G2Affine,
    _marker: PhantomData<E>,
}

impl<E: PairingEngine> Digestible for AccValue<E> {
    fn to_digest(&self) -> Digest {
        ark_ff::to_bytes!(self.g_s, self.g_r, self.h_s_r, self.h_r_s)
            .expect("failed to convert acc to bytes")
            .to_digest()
    }
}

impl<E: PairingEngine> Add for AccValue<E> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self {
            g_s: self.g_s + rhs.g_s,
            g_r: self.g_r + rhs.g_r,
            h_s_r: self.h_s_r + rhs.h_s_r,
            h_r_s: self.h_r_s + rhs.h_r_s,
            _marker: PhantomData,
        }
    }
}

impl<E: PairingEngine> Sub for AccValue<E> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self {
            g_s: self.g_s + (-rhs.g_s),
            g_r: self.g_r + (-rhs.g_r),
            h_s_r: self.h_s_r + (-rhs.h_s_r),
            h_r_s: self.h_r_s + (-rhs.h_r_s),
            _marker: PhantomData,
        }
    }
}

impl<E: PairingEngine> AccValue<E> {
    /// Compute accumulative value from set using public key.
    pub fn from_set(set: &Set, pk: &AccPublicKey<E>) -> Self {
        let g_s = cal_acc_g_pk::<E, _>(set, |i| {
            pk.get_g_s_i(i)
                .unwrap_or_else(|| panic!("failed to access get_g_s_i, i = {}", i))
        });
        let g_r = cal_acc_g_pk::<E, _>(set, |i| {
            pk.get_g_r_i(i)
                .unwrap_or_else(|| panic!("failed to access get_g_r_i, i = {}", i))
        });
        let h_s_r = cal_acc_h_pk::<E, _>(set, |i| {
            pk.get_h_r_i_s_j(pk.q - i, i).unwrap_or_else(|| {
                panic!(
                    "failed to access get_h_r_i_s_j, i = {}, j = {}",
                    pk.q - i,
                    i
                )
            })
        });
        let h_r_s = cal_acc_h_pk::<E, _>(set, |i| {
            pk.get_h_r_i_s_j(i, pk.q - i).unwrap_or_else(|| {
                panic!(
                    "failed to access get_h_r_i_s_j, i = {}, j = {}",
                    i,
                    pk.q - i
                )
            })
        });

        Self {
            g_s,
            g_r,
            h_s_r,
            h_r_s,
            _marker: PhantomData,
        }
    }

    /// Compute accumulative value from set using secret key.
    pub fn from_set_sk(set: &Set, sk: &AccSecretKeyWithPowCache<E>, q: u64) -> Self {
        let q_fr = E::Fr::from(q);
        let g_s = {
            let x = cal_acc_sk::<E, _>(set, |i| sk.s_pow.apply(&E::Fr::from(i)));
            sk.g_pow.apply(&x).into_affine()
        };
        let g_r = {
            let x = cal_acc_sk::<E, _>(set, |i| sk.r_pow.apply(&E::Fr::from(i)));
            sk.g_pow.apply(&x).into_affine()
        };
        let h_s_r = {
            let x = cal_acc_sk::<E, _>(set, |i| {
                let i_fr = E::Fr::from(i);
                let s_i = sk.s_pow.apply(&i_fr);
                let r_q_i = sk.r_pow.apply(&(q_fr - i_fr));
                s_i * r_q_i
            });
            sk.h_pow.apply(&x).into_affine()
        };
        let h_r_s = {
            let x = cal_acc_sk::<E, _>(set, |i| {
                let i_fr = E::Fr::from(i);
                let r_i = sk.r_pow.apply(&i_fr);
                let s_q_i = sk.s_pow.apply(&(q_fr - i_fr));
                r_i * s_q_i
            });
            sk.h_pow.apply(&x).into_affine()
        };

        Self {
            g_s,
            g_r,
            h_s_r,
            h_r_s,
            _marker: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{acc::keys::AccSecretKey, set};
    use ark_bls12_381::Bls12_381;

    #[test]
    fn test_compute_acc() {
        let mut rng = rand::thread_rng();
        let q = 5;
        let sk = AccSecretKey::<Bls12_381>::rand(&mut rng).into();
        let pk = AccPublicKey::<Bls12_381>::gen_key(&sk, q);

        let s = set! {1, 2, 3};
        let acc1 = AccValue::<Bls12_381>::from_set(&s, &pk);
        let acc2 = AccValue::<Bls12_381>::from_set_sk(&s, &sk, q);
        assert_eq!(acc1, acc2);
    }

    #[test]
    fn test_update_acc() {
        let mut rng = rand::thread_rng();
        let q = 5;
        let sk = AccSecretKey::<Bls12_381>::rand(&mut rng).into();

        let acc1 = AccValue::<Bls12_381>::from_set_sk(&set! {1, 2, 3}, &sk, q);
        let acc2 = AccValue::<Bls12_381>::from_set_sk(&set! {1, 2}, &sk, q);
        let acc3 = AccValue::<Bls12_381>::from_set_sk(&set! {3}, &sk, q);
        assert_eq!(acc1, acc2 + acc3);
        assert_eq!(acc1 - acc2, acc3);
    }
}
