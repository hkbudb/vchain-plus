use acc_benchmark::*;
use criterion::{criterion_group, criterion_main, Criterion};
use pprof::criterion::{Output, PProfProfiler};

const Q: u64 = 4096;
const TEST_SET_SIZE: u64 = 100;

macro_rules! use_fixture {
    ($x: expr) => {
        ($x)(once_cell::sync::Lazy::force(&F_BN254))
    };
}

prepare_fixtures!(Q);

pub fn prof_cal_acc(c: &mut Criterion) {
    let mut group = c.benchmark_group("prof_cal_acc");
    let set = generate_set(TEST_SET_SIZE);
    use_fixture!(|fixture: &Fixture<_>| {
        fixture.bench_cal_acc(&mut group, &set);
    });
    group.finish();
}

pub fn prof_update_acc(c: &mut Criterion) {
    let mut group = c.benchmark_group("prof_update_acc");
    use_fixture!(|fixture: &Fixture<_>| {
        fixture.bench_update_acc(&mut group);
    });
    group.finish();
}

pub fn prof_gen_intermediate_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("prof_gen_intermediate");
    let (set1, set2) = generate_two_sets(TEST_SET_SIZE);
    use_fixture!(|fixture: &Fixture<_>| {
        fixture.bench_gen_intermediate_proof(&mut group, &set1, &set2);
    });
    group.finish();
}

pub fn prof_verify_intermediate_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("prof_verify_intermediate");
    let (set1, set2) = generate_two_sets(TEST_SET_SIZE);
    use_fixture!(|fixture: &Fixture<_>| {
        fixture.bench_verify_intermediate_proof(&mut group, &set1, &set2);
    });
    group.finish();
}

pub fn prof_gen_final_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("prof_gen_final");
    let (set1, set2) = generate_two_sets(TEST_SET_SIZE);
    use_fixture!(|fixture: &Fixture<_>| {
        fixture.bench_gen_final_proof(&mut group, &set1, &set2);
    });
    group.finish();
}

pub fn prof_verify_final_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("prof_verify_final");
    let (set1, set2) = generate_two_sets(TEST_SET_SIZE);
    use_fixture!(|fixture: &Fixture<_>| {
        fixture.bench_verify_final_proof(&mut group, &set1, &set2);
    });
    group.finish();
}

criterion_group!(
    name = prof;
    config = Criterion::default().with_profiler(PProfProfiler::new(1_000, Output::Flamegraph(None)));
    targets = prof_cal_acc, prof_update_acc, prof_gen_intermediate_proof, prof_verify_intermediate_proof, prof_gen_final_proof, prof_verify_final_proof
);
criterion_main!(prof);
