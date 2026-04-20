# ristretto255

WIP verified implementation of the [ristretto255](https://ristretto.group/) prime-order group.

**DO NOT USE.** Adapted from [`curve25519-dalek`](https://github.com/dalek-cryptography/curve25519-dalek) but using verified Rust derived from the [HACL\*](https://github.com/hacl-star/hacl-star) project via the [`libcrux-hacl-rs`](https://github.com/cryspen/libcrux) crate.

## Usage

```rust
use ristretto255::{RistrettoPoint, Scalar};

let bp = RistrettoPoint::basepoint();
let k = Scalar::from_bytes_mod_order(&[7u8; 32]);

let point = &k * &bp;
let encoded = point.compress();
let decoded = encoded.decompress().unwrap();

assert_eq!(point, decoded);
```

## Status

Implemented: decompression, compression, point addition, variable-base scalar multiplication, `from_uniform_bytes` (via Elligator).

Not yet implemented: fixed-base scalar multiplication, multiscalar multiplication, variable-time variants.

## Verification

Field and scalar arithmetic come from `libcrux-hacl-rs`, which is extracted from verified F\* code in HACL\*. The Ristretto-layer Rust code in this crate is progressively being annotated with [hax](https://github.com/hacspec/hax) for extraction and F\* proofs.

## Benchmarks

```
cd ristretto255
cargo bench
```

Measured on a 2023 MacBook Pro M2 (12-core, 32 GB):

| Operation | ristretto255 | curve25519-dalek v4.1 |
| --- | ---: | ---: |
| Point compression | ~4.7 µs | ~2.2 µs |
| Point decompression | ~4.8 µs | ~2.2 µs |
| Scalar multiplication | ~30.8 µs | ~18.9 µs |
