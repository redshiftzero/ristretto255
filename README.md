# ristretto255
WIP verified implementation of the ristretto255 prime-order group

DO NOT USE!

Adapted from `curve25519-dalek` but using verified Rust derived from the [HACL*](https://github.com/hacl-star/hacl-star) project via the `libcrux-hacl-rs` crate

# Benchmarks

Run `criterion` benchmarks via:

```
cd ristretto255
cargo bench
```

Benchmarks were computed on a 2023 Macbook Pro M2 (12 core CPU) with 32 GB memory.

| Operation | ristretto255 | curve25519-dalek |
| --- | ---: | ---: |
| Point compression | ~4.7 us | ~2.2 us |
| Point decompression | ~4.8 us | ~2.2 us |



