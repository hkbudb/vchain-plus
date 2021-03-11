use super::{
    keys::{AccPublicKey, AccSecretKeyWithPowCache},
    set::Set,
};
use crate::digest::{concat_digest_ref, Digest, Digestible};
use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ff::Zero;
use core::{
    marker::PhantomData,
    ops::{Add, Sub},
};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

/// An accumulative value computed by g^{\sum s^i}.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeftAccValue<E: PairingEngine> {
    /// g^{\sum s^i}
    #[serde(with = "super::serde_impl")]
    value: E::G1Affine,
    _marker: PhantomData<E>,
}

impl<E: PairingEngine> Digestible for LeftAccValue<E> {
    fn to_digest(&self) -> Digest {
        ark_ff::to_bytes!(self.value)
            .expect("failed to convert acc to bytes")
            .to_digest()
    }
}

impl<E: PairingEngine> Add for LeftAccValue<E> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self {
            value: self.value + rhs.value,
            _marker: PhantomData,
        }
    }
}

impl<E: PairingEngine> Sub for LeftAccValue<E> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self {
            value: self.value + (-rhs.value),
            _marker: PhantomData,
        }
    }
}

impl<E: PairingEngine> LeftAccValue<E> {
    /// Compute accumulative value from set using public key.
    pub fn from_set(set: &Set, pk: &AccPublicKey<E>) -> Self {
        let value = set
            .par_iter()
            .map(|&i| {
                pk.get_g_s_i(i.get())
                    .unwrap_or_else(|| panic!("failed to access get_g_s_i, i = {}", i))
            })
            .fold(E::G1Projective::zero, |a, b| a.add_mixed(&b))
            .reduce(E::G1Projective::zero, |a, b| a + b)
            .into_affine();
        Self {
            value,
            _marker: PhantomData,
        }
    }

    /// Compute accumulative value from set using secret key.
    pub fn from_set_sk(set: &Set, sk: &AccSecretKeyWithPowCache<E>, _q: u64) -> Self {
        let x = set
            .par_iter()
            .map(|&i| {
                let i_fr = E::Fr::from(i.get());
                sk.s_pow.apply(&i_fr)
            })
            .reduce(E::Fr::zero, |a, b| a + b);
        let value = sk.g_pow.apply(&x).into_affine();
        Self {
            value,
            _marker: PhantomData,
        }
    }
}

/// An accumulative value computed by h^{\sum r^i \cdot s^{q - i}}.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RightAccValue<E: PairingEngine> {
    /// h^{\sum r^i \cdot s^{q - i}}
    #[serde(with = "super::serde_impl")]
    value: E::G2Affine,
    _marker: PhantomData<E>,
}

impl<E: PairingEngine> Digestible for RightAccValue<E> {
    fn to_digest(&self) -> Digest {
        ark_ff::to_bytes!(self.value)
            .expect("failed to convert acc to bytes")
            .to_digest()
    }
}

impl<E: PairingEngine> Add for RightAccValue<E> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self {
            value: self.value + rhs.value,
            _marker: PhantomData,
        }
    }
}

impl<E: PairingEngine> Sub for RightAccValue<E> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self {
            value: self.value + (-rhs.value),
            _marker: PhantomData,
        }
    }
}

impl<E: PairingEngine> RightAccValue<E> {
    /// Compute accumulative value from set using public key.
    pub fn from_set(set: &Set, pk: &AccPublicKey<E>) -> Self {
        let value = set
            .par_iter()
            .map(|&i| {
                let i = i.get();
                let j = pk.q - i;
                pk.get_h_r_i_s_j(i, j).unwrap_or_else(|| {
                    panic!("failed to access get_h_r_i_s_j, i = {}, j = {}", i, j)
                })
            })
            .fold(E::G2Projective::zero, |a, b| a.add_mixed(&b))
            .reduce(E::G2Projective::zero, |a, b| a + b)
            .into_affine();
        Self {
            value,
            _marker: PhantomData,
        }
    }

    /// Compute accumulative value from set using secret key.
    pub fn from_set_sk(set: &Set, sk: &AccSecretKeyWithPowCache<E>, q: u64) -> Self {
        let q_fr = E::Fr::from(q);
        let x = set
            .par_iter()
            .map(|&i| {
                let i_fr = E::Fr::from(i.get());
                let r_i = sk.r_pow.apply(&i_fr);
                let s_q_i = sk.s_pow.apply(&(q_fr - i_fr));
                r_i * s_q_i
            })
            .reduce(E::Fr::zero, |a, b| a + b);
        let value = sk.h_pow.apply(&x).into_affine();
        Self {
            value,
            _marker: PhantomData,
        }
    }
}

/// An accumulative value consists of both [`LeftAccValue`] and [`RightAccValue`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AccValue<E: PairingEngine> {
    /// g^{\sum s^i}
    left: LeftAccValue<E>,
    /// h^{\sum r^i \cdot s^{q - i}}
    right: RightAccValue<E>,
}

impl<E: PairingEngine> Digestible for AccValue<E> {
    fn to_digest(&self) -> Digest {
        concat_digest_ref([self.left.to_digest(), self.right.to_digest()].iter())
    }
}

impl<E: PairingEngine> Add for AccValue<E> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self {
            left: self.left + rhs.left,
            right: self.right + rhs.right,
        }
    }
}

impl<E: PairingEngine> Sub for AccValue<E> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self {
            left: self.left - rhs.left,
            right: self.right - rhs.right,
        }
    }
}

impl<E: PairingEngine> AccValue<E> {
    /// Compute accumulative value from set using public key.
    pub fn from_set(set: &Set, pk: &AccPublicKey<E>) -> Self {
        Self {
            left: LeftAccValue::from_set(set, pk),
            right: RightAccValue::from_set(set, pk),
        }
    }

    /// Compute accumulative value from set using secret key.
    pub fn from_set_sk(set: &Set, sk: &AccSecretKeyWithPowCache<E>, q: u64) -> Self {
        Self {
            left: LeftAccValue::from_set_sk(set, sk, q),
            right: RightAccValue::from_set_sk(set, sk, q),
        }
    }

    /// Return left half of accumulative value.
    pub fn get_left(&self) -> LeftAccValue<E> {
        self.left
    }

    /// Return right half of accumulative value.
    pub fn get_right(&self) -> RightAccValue<E> {
        self.right
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
