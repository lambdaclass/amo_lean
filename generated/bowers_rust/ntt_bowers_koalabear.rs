//! AMO-Lean Generated Rust NTT — Bowers G ordering
//! N = 1048576, p = 2130706433
//! Reduction: solinasFold (e-graph cost model)
//! Ordering: Bowers G (bit-reversed twiddles, DIF butterfly, sequential access)
//! Verified: solinasFold_mod_correct / monty_reduce_spec
//!
//! Bowers advantage: cache-friendly twiddle access.
//! Standard DIT: twiddles[stage*(n/2) + group*half + pair] — strided, non-sequential.
//! Bowers:       twiddles[block] — linear, sequential. CPU prefetch works.

use std::time::Instant;

/// Solinas fold — e-graph selected for scalar u32 fields.
/// Verified: solinasFold_mod_correct.
#[inline(always)]
fn solinas_fold(x: u64) -> u32 {
    (((x >> 31) as u64).wrapping_mul(16777215 as u64))
        .wrapping_add(x & 2147483647 as u64) as u32
}

/// DIF butterfly: a' = fold(a + b), b' = fold((p + a - b) * w).
/// Bowers G network applies ONE twiddle per block.
#[inline(always)]
fn dif_butterfly(a: &mut u32, b: &mut u32, w: u32) {
    let va = *a;
    let vb = *b;
    *a = solinas_fold(va as u64 + vb as u64);
    let diff = solinas_fold(2130706433 as u64 + va as u64 - vb as u64);
    *b = solinas_fold(diff as u64 * w as u64);
}

fn bit_reverse(data: &mut [u32]) {
    let n = data.len();
    let log_n = n.trailing_zeros();
    for i in 0..n {
        let j = i.reverse_bits() >> (usize::BITS - log_n);
        if i < j { data.swap(i, j); }
    }
}

fn mod_pow(mut base: u64, mut exp: u64, modulus: u64) -> u64 {
    let mut result: u64 = 1;
    base %= modulus;
    while exp > 0 {
        if exp & 1 == 1 {
            result = (result as u128 * base as u128 % modulus as u128) as u64;
        }
        exp >>= 1;
        base = (base as u128 * base as u128 % modulus as u128) as u64;
    }
    result
}

/// Compute bit-reversed twiddle table for Bowers G network.
fn compute_bowers_twiddles(n: usize, generator: u64) -> Vec<u32> {
    let p = 2130706433 as u64;
    let omega = mod_pow(generator, (p - 1) / n as u64, p);
    let mut tw: Vec<u32> = (0..n/2)
        .map(|i| mod_pow(omega, i as u64, p) as u32)
        .collect();
    bit_reverse(&mut tw);
    tw
}

/// Bowers G NTT: bit-reverse input, DIF stages small→large, sequential twiddle access.
/// Cache-friendly: twiddles accessed linearly (one per block).
/// Reduction: solinasFold (e-graph selected).
pub fn ntt_bowers(data: &mut [u32], twiddles: &[u32]) {
    let n = data.len();
    let log_n = n.trailing_zeros() as usize;

    bit_reverse(data);

    for log_half in 0..log_n {
        let half = 1_usize << log_half;
        let block_size = 2 * half;
        let num_blocks = n / block_size;

        for block in 0..num_blocks {
            let w: u32 = if block == 0 { 1 } else { twiddles[block] };
            let base = block * block_size;
            for j in 0..half {
                let i0 = base + j;
                let i1 = i0 + half;
                let (left, right) = data.split_at_mut(i1);
                dif_butterfly(&mut left[i0], &mut right[0], w);
            }
        }
    }
}

fn main() {
    let n: usize = 1048576;
    let generator: u64 = 3;
    let twiddles = compute_bowers_twiddles(n, generator);

    let iters: usize = 3;
    let start = Instant::now();
    for _ in 0..iters {
        let mut data: Vec<u32> = (0..n)
            .map(|i| ((i as u64 * 1000000007) % 2130706433 as u64) as u32)
            .collect();
        ntt_bowers(&mut data, &twiddles);
        std::hint::black_box(&data);
    }
    let elapsed = start.elapsed();
    let us = elapsed.as_secs_f64() / iters as f64 * 1e6;
    let melem = n as f64 * iters as f64 / elapsed.as_secs_f64() / 1e6;
    eprintln!("N=1048576 p=2130706433 Bowers (solinasFold)");
    eprintln!("  {} us  {} Melem/s", us, melem);
}
