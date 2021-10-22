use ark_ec::PairingEngine;
use criterion::{black_box, measurement::Measurement, BenchmarkGroup, BenchmarkId};
use rand::{prelude::*, rngs::StdRng};
use vchain_plus::{
    acc::{
        acc_value::AccValue,
        keys::{AccPublicKey, AccSecretKey, AccSecretKeyWithPowCache},
        ops::{compute_set_operation_final, compute_set_operation_intermediate, Op},
        Set,
    },
    set,
};

pub fn generate_set(size: u64) -> Set {
    (1..=size).collect()
}

pub fn generate_two_sets(size: u64) -> (Set, Set) {
    let half_size = size / 2;
    assert!(half_size > 0);
    (
        (1..=size).collect(),
        (half_size..=size + half_size).collect(),
    )
}

pub struct Fixture<E: PairingEngine> {
    pub curve_name: &'static str,
    pub sk: AccSecretKeyWithPowCache<E>,
    pub pk: AccPublicKey<E>,
}

impl<E: PairingEngine> Fixture<E> {
    pub fn new(curve_name: &'static str, q: u64) -> Self {
        let mut rng = StdRng::seed_from_u64(123_456_789u64);
        let sk = AccSecretKey::<E>::rand(&mut rng).into();
        let pk = AccPublicKey::<E>::gen_key(&sk, q);
        Self { curve_name, sk, pk }
    }

    pub fn bench_cal_acc<'a, M: Measurement>(&self, group: &mut BenchmarkGroup<'a, M>, s: &Set) {
        group.bench_with_input(BenchmarkId::new(self.curve_name, s.len()), s, |b, s| {
            b.iter(|| black_box(AccValue::from_set(s, &self.pk)))
        });
    }

    pub fn bench_update_acc<'a, M: Measurement>(&self, group: &mut BenchmarkGroup<'a, M>) {
        let acc1 = AccValue::from_set(&set! {1}, &self.pk);
        let acc2 = AccValue::from_set(&set! {2}, &self.pk);
        group.bench_function(self.curve_name, |b| b.iter(|| black_box(acc1 + acc2)));
    }

    pub fn bench_gen_intermediate_proof<'a, M: Measurement>(
        &self,
        group: &mut BenchmarkGroup<'a, M>,
        s1: &Set,
        s2: &Set,
    ) {
        let acc1 = AccValue::from_set_sk(s1, &self.sk, self.pk.get_q());
        let acc2 = AccValue::from_set_sk(s2, &self.sk, self.pk.get_q());
        group.bench_with_input(
            BenchmarkId::new(self.curve_name, s1.len()),
            &(s1, acc1, s2, acc2),
            |b, (s1, acc1, s2, acc2)| {
                b.iter(|| {
                    black_box(compute_set_operation_intermediate(
                        Op::Intersection,
                        s1,
                        acc1,
                        s2,
                        acc2,
                        &self.pk,
                    ))
                })
            },
        );
    }

    pub fn bench_verify_intermediate_proof<'a, M: Measurement>(
        &self,
        group: &mut BenchmarkGroup<'a, M>,
        s1: &Set,
        s2: &Set,
    ) {
        let acc1 = AccValue::from_set_sk(s1, &self.sk, self.pk.get_q());
        let acc2 = AccValue::from_set_sk(s2, &self.sk, self.pk.get_q());
        let (_s3, acc3, proof) =
            compute_set_operation_intermediate(Op::Intersection, s1, &acc1, s2, &acc2, &self.pk);
        group.bench_with_input(
            BenchmarkId::new(self.curve_name, s1.len()),
            &(acc1, acc2, acc3),
            |b, (acc1, acc2, acc3)| b.iter(|| black_box(proof.verify(acc1, acc2, acc3, &self.pk))),
        );
    }

    pub fn bench_gen_final_proof<'a, M: Measurement>(
        &self,
        group: &mut BenchmarkGroup<'a, M>,
        s1: &Set,
        s2: &Set,
    ) {
        group.bench_with_input(
            BenchmarkId::new(self.curve_name, s1.len()),
            &(s1, s2),
            |b, (s1, s2)| {
                b.iter(|| {
                    black_box(compute_set_operation_final(
                        Op::Intersection,
                        s1,
                        s2,
                        &self.pk,
                    ))
                })
            },
        );
    }

    pub fn bench_verify_final_proof<'a, M: Measurement>(
        &self,
        group: &mut BenchmarkGroup<'a, M>,
        s1: &Set,
        s2: &Set,
    ) {
        let acc1 = AccValue::from_set_sk(s1, &self.sk, self.pk.get_q());
        let acc2 = AccValue::from_set_sk(s2, &self.sk, self.pk.get_q());
        let (s3, proof) = compute_set_operation_final(Op::Intersection, s1, s2, &self.pk);
        group.bench_with_input(
            BenchmarkId::new(self.curve_name, s1.len()),
            &(acc1, acc2, s3),
            |b, (acc1, acc2, s3)| b.iter(|| black_box(proof.verify(acc1, acc2, s3, &self.pk))),
        );
    }
}

#[macro_export]
macro_rules! prepare_fixtures {
    ($q: expr) => {
        $crate::prepare_fixtures!(F_BLS12_377, ark_bls12_377::Bls12_377, $q);
        $crate::prepare_fixtures!(F_BLS12_381, ark_bls12_381::Bls12_381, $q);
        $crate::prepare_fixtures!(F_BN254, ark_bn254::Bn254, $q);
        $crate::prepare_fixtures!(F_BW6_761, ark_bw6_761::BW6_761, $q);
        $crate::prepare_fixtures!(F_CP6_782, ark_cp6_782::CP6_782, $q);
        $crate::prepare_fixtures!(F_MNT4_298, ark_mnt4_298::MNT4_298, $q);
        $crate::prepare_fixtures!(F_MNT4_753, ark_mnt4_753::MNT4_753, $q);
        $crate::prepare_fixtures!(F_MNT6_298, ark_mnt6_298::MNT6_298, $q);
        $crate::prepare_fixtures!(F_MNT6_753, ark_mnt6_753::MNT6_753, $q);
    };

    ($name: ident, $curve: ty, $q: expr) => {
        static $name: once_cell::sync::Lazy<$crate::Fixture<$curve>> =
            once_cell::sync::Lazy::new(|| {
                let curve_name = stringify!($curve)
                    .split(':')
                    .next()
                    .unwrap()
                    .strip_prefix("ark_")
                    .unwrap();
                println!("prepare fixture for {}...", curve_name);
                let ret = $crate::Fixture::new(curve_name, $q);
                println!("prepare fixture for {} done", curve_name);
                ret
            });
    };
}

#[macro_export]
macro_rules! iterate_fixtures {
    ($x: expr) => {
        $crate::iterate_fixtures!(F_BLS12_377, $x);
        $crate::iterate_fixtures!(F_BLS12_381, $x);
        $crate::iterate_fixtures!(F_BN254, $x);
        $crate::iterate_fixtures!(F_BW6_761, $x);
        $crate::iterate_fixtures!(F_CP6_782, $x);
        $crate::iterate_fixtures!(F_MNT4_298, $x);
        $crate::iterate_fixtures!(F_MNT4_753, $x);
        $crate::iterate_fixtures!(F_MNT6_298, $x);
        $crate::iterate_fixtures!(F_MNT6_753, $x);
    };

    ($name: ident, $x: expr) => {
        ($x)(once_cell::sync::Lazy::force(&$name))
    };
}
