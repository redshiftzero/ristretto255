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

fn bench_decompress_ours(c: &mut Criterion) {
    let bp_compressed = ristretto255::constants::RISTRETTO_BASEPOINT_COMPRESSED;
    c.bench_function("ristretto255::CompressedRistretto::decompress", |b| {
        b.iter(|| bp_compressed.decompress().unwrap())
    });
}

fn bench_decompress_dalek(c: &mut Criterion) {
    let bp_compressed = curve25519_dalek::constants::RISTRETTO_BASEPOINT_COMPRESSED;
    c.bench_function("dalek::CompressedRistretto::decompress", |b| {
        b.iter(|| bp_compressed.decompress().unwrap())
    });
}

criterion_group!(
    benches,
    bench_compress_ours,
    bench_compress_dalek,
    bench_decompress_ours,
    bench_decompress_dalek,
);
criterion_main!(benches);
