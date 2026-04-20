use criterion::{criterion_group, criterion_main, Criterion};

fn bench_compress_ours(c: &mut Criterion) {
    let bp = ristretto255::RistrettoPoint::basepoint();
    c.bench_function("ristretto255::RistrettoPoint::compress", |b| {
        b.iter(|| bp.compress())
    });
}

fn bench_compress_dalek(c: &mut Criterion) {
    let bp = curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
    c.bench_function("dalek::RistrettoPoint::compress", |b| {
        b.iter(|| bp.compress())
    });
}

criterion_group!(benches, bench_compress_ours, bench_compress_dalek);
criterion_main!(benches);
