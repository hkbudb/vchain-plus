use acc_benchmark::*;
use criterion::{criterion_group, criterion_main, Criterion};

const Q: u64 = 2048;
const TEST_SET_SIZE: &[u64] = &[40, 50, 60];
prepare_fixtures!(Q);

pub fn bench_cal_acc(c: &mut Criterion) {
    let mut group = c.benchmark_group("cal_acc");
    for i in TEST_SET_SIZE {
        let set = generate_set(*i);
        iterate_fixtures!(|fixture: &Fixture<_>| {
            fixture.bench_cal_acc(&mut group, &set);
        });
    }
    group.finish();
}

pub fn bench_update_acc(c: &mut Criterion) {
    let mut group = c.benchmark_group("update_acc");
    iterate_fixtures!(|fixture: &Fixture<_>| {
        fixture.bench_update_acc(&mut group);
    });
    group.finish();
}

pub fn bench_gen_intermediate_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("gen_intermediate");
    for i in TEST_SET_SIZE {
        let (set1, set2) = generate_two_sets(*i);
        iterate_fixtures!(|fixture: &Fixture<_>| {
            fixture.bench_gen_intermediate_proof(&mut group, &set1, &set2);
        });
    }
    group.finish();
}

pub fn bench_verify_intermediate_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("verify_intermediate");
    for i in TEST_SET_SIZE {
        let (set1, set2) = generate_two_sets(*i);
        iterate_fixtures!(|fixture: &Fixture<_>| {
            fixture.bench_verify_intermediate_proof(&mut group, &set1, &set2);
        });
    }
    group.finish();
}

pub fn bench_gen_final_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("gen_final");
    for i in TEST_SET_SIZE {
        let (set1, set2) = generate_two_sets(*i);
        iterate_fixtures!(|fixture: &Fixture<_>| {
            fixture.bench_gen_final_proof(&mut group, &set1, &set2);
        });
    }
    group.finish();
}

pub fn bench_verify_final_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("verify_final");
    for i in TEST_SET_SIZE {
        let (set1, set2) = generate_two_sets(*i);
        iterate_fixtures!(|fixture: &Fixture<_>| {
            fixture.bench_verify_final_proof(&mut group, &set1, &set2);
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_cal_acc,
    bench_update_acc,
    bench_gen_intermediate_proof,
    bench_verify_intermediate_proof,
    bench_gen_final_proof,
    bench_verify_final_proof,
);
criterion_main!(benches);
