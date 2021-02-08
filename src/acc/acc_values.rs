use crate::digest::{concat_digest_ref, Digest, Digestible};
use ark_ec::PairingEngine;
use core::marker::PhantomData;
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
