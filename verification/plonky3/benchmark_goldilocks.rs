//! Standalone Goldilocks NTT benchmark using Plonky3.
//! Compiles as a binary (not cdylib) for direct execution.
//! Uses Plonky3's Radix2Dit with the standard Goldilocks field.
//!
//! Build: rustc -O benchmark_goldilocks.rs --edition 2021 \
//!   -L plonky3_shim/target/release/deps \
//!   --extern p3_goldilocks=... --extern p3_dft=... ...
//!
//! This is complex, so we use the shim dylib instead.

use std::time::Instant;

// FFI to the shim
extern "C" {
    fn plonky3_ntt_forward(data: *mut u64, len: usize) -> i32;
}

const GOLDI_P: u64 = 0xFFFF_FFFF_0000_0001;

fn mod_pow(mut base: u64, mut exp: u64, m: u64) -> u64 {
    let mut result: u128 = 1;
    let mut b: u128 = base as u128 % m as u128;
    while exp > 0 {
        if exp & 1 == 1 {
            result = (result * b) % m as u128;
        }
        b = (b * b) % m as u128;
        exp >>= 1;
    }
    result as u64
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let log_n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(20);
    let n: usize = 1 << log_n;
    let iters: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(10);

    let mut data: Vec<u64> = (0..n)
        .map(|i| ((i as u128 * 1000000007) % GOLDI_P as u128) as u64)
        .collect();
    let orig = data.clone();

    // Warmup
    unsafe { plonky3_ntt_forward(data.as_mut_ptr(), n); }

    // Benchmark
    let mut total_us = 0.0_f64;
    for _ in 0..iters {
        data.copy_from_slice(&orig);
        let t0 = Instant::now();
        unsafe { plonky3_ntt_forward(data.as_mut_ptr(), n); }
        total_us += t0.elapsed().as_micros() as f64;
    }
    let avg_us = total_us / iters as f64;
    let melem = n as f64 / avg_us;

    println!("Plonky3 Goldilocks NTT (N=2^{} = {}, {} iters): {:.1} µs ({:.1} Melem/s)",
        log_n, n, iters, avg_us, melem);
}
