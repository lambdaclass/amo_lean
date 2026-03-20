//! AMO-Lean Generated Rust NTT — Bowers G ordering
//! N = 1048576, p = 18446744069414584321
//! Reduction: solinasFold (e-graph cost model)
//! Ordering: Bowers G (bit-reversed twiddles, DIF butterfly, sequential access)
//! Verified: solinasFold_mod_correct / monty_reduce_spec
//!
//! Bowers advantage: cache-friendly twiddle access.
//! Standard DIT: twiddles[stage*(n/2) + group*half + pair] — strided, non-sequential.
//! Bowers:       twiddles[block] — linear, sequential. CPU prefetch works.

use std::time::Instant;

/// Goldilocks reduction — exploits p = 2^64 - 2^32 + 1.
/// Verified: solinasFold_mod_correct (Goldilocks instance).
#[inline(always)]
fn goldilocks_reduce(x: u128) -> u64 {
    let lo = x as u64;
    let hi = (x >> 64) as u64;
    let hh = hi >> 32;
    let hl = hi & 0xFFFFFFFF_u64;
    let (t0, borrow) = lo.overflowing_sub(hh);
    let t0 = if borrow { t0.wrapping_sub(0xFFFFFFFF_u64) } else { t0 };
    let t1 = hl.wrapping_mul(0xFFFFFFFF_u64);
    let (result, carry) = t0.overflowing_add(t1);
    if carry || result >= 18446744069414584321_u64 { result.wrapping_sub(18446744069414584321_u64) } else { result }
}

/// DIF butterfly for Goldilocks.
#[inline(always)]
fn dif_butterfly(a: &mut u64, b: &mut u64, w: u64) {
    let va = *a;
    let vb = *b;
    let sum = va.wrapping_add(vb);
    *a = if sum >= 18446744069414584321_u64 { sum - 18446744069414584321_u64 } else { sum };
    *b = goldilocks_reduce(
        (if va >= vb { va - vb } else { 18446744069414584321_u64 - vb + va }) as u128
        * w as u128);
}

fn bit_reverse(data: &mut [u64]) {
    let n = data.len();
    let log_n = n.trailing_zeros();
    for i in 0..n {
        let j = i.reverse_bits() >> (usize::BITS - log_n);
        if i < j { data.swap(i, j); }
    }
}

fn mod_pow(mut base: u128, mut exp: u128, modulus: u128) -> u128 {
    let mut result: u128 = 1;
    base %= modulus;
    while exp > 0 {
        if exp & 1 == 1 {
            result = (result as u128 * base as u128 % modulus as u128) as u128;
        }
        exp >>= 1;
        base = (base as u128 * base as u128 % modulus as u128) as u128;
    }
    result
}

/// Compute bit-reversed twiddle table for Bowers G network.
fn compute_bowers_twiddles(n: usize, generator: u128) -> Vec<u64> {
    let p = 18446744069414584321 as u128;
    let omega = mod_pow(generator, (p - 1) / n as u128, p);
    let mut tw: Vec<u64> = (0..n/2)
        .map(|i| mod_pow(omega, i as u128, p) as u64)
        .collect();
    bit_reverse(&mut tw);
    tw
}

/// Bowers G NTT: bit-reverse input, DIF stages small→large, sequential twiddle access.
/// Cache-friendly: twiddles accessed linearly (one per block).
/// Reduction: solinasFold (e-graph selected).
pub fn ntt_bowers(data: &mut [u64], twiddles: &[u64]) {
    let n = data.len();
    let log_n = n.trailing_zeros() as usize;

    bit_reverse(data);

    for log_half in 0..log_n {
        let half = 1_usize << log_half;
        let block_size = 2 * half;
        let num_blocks = n / block_size;

        for block in 0..num_blocks {
            let w: u64 = if block == 0 { 1 } else { twiddles[block] };
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
    let generator: u128 = 7;
    let twiddles = compute_bowers_twiddles(n, generator);

    let iters: usize = 3;
    let start = Instant::now();
    for _ in 0..iters {
        let mut data: Vec<u64> = (0..n)
            .map(|i| ((i as u128 * 1000000007) % 18446744069414584321 as u128) as u64)
            .collect();
        ntt_bowers(&mut data, &twiddles);
        std::hint::black_box(&data);
    }
    let elapsed = start.elapsed();
    let us = elapsed.as_secs_f64() / iters as f64 * 1e6;
    let melem = n as f64 * iters as f64 / elapsed.as_secs_f64() / 1e6;
    eprintln!("N=1048576 p=18446744069414584321 Bowers (solinasFold)");
    eprintln!("  {} us  {} Melem/s", us, melem);
}
