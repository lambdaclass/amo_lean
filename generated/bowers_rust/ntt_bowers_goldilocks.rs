//! AMO-Lean Generated Rust NTT — Bowers G ordering
//! Field: Goldilocks (p = 2^64 - 2^32 + 1)
//! Reduction: Goldilocks reduce (e-graph cost model selected)
//! Ordering: Bowers G (bit-reversed twiddles, DIF butterfly, sequential access)
//! Verified in Lean 4: solinasFold_mod_correct (0 sorry, 0 axioms)
//!
//! HOW TO BUILD AND RUN:
//!   rustc -O ntt_bowers_goldilocks.rs -o ntt_bench && ./ntt_bench
//!
//! The -O flag is REQUIRED. Without it, Rust runs in debug mode (10-50x slower).

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
/// Uses overflowing_add to correctly handle sum >= 2^64.
#[inline(always)]
fn dif_butterfly(a: &mut u64, b: &mut u64, w: u64) {
    let va = *a;
    let vb = *b;
    let (sum, overflow) = va.overflowing_add(vb);
    *a = if overflow || sum >= 18446744069414584321_u64 { sum.wrapping_sub(18446744069414584321_u64) } else { sum };
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
    let p: u128 = 0xFFFFFFFF00000001;
    let sizes: &[(usize, usize)] = &[
        (1 << 14, 200), (1 << 16, 50), (1 << 18, 20), (1 << 20, 10), (1 << 22, 3),
    ];
    println!("AMO-Lean Bowers NTT — Goldilocks (p = 2^64 - 2^32 + 1)");
    println!("Reduction: Goldilocks reduce (e-graph selected, verified in Lean 4)");
    println!("Build: rustc -O ntt_bowers_goldilocks.rs -o ntt_bench && ./ntt_bench");
    println!();
    println!("{:>8} {:>12} {:>12} {:>10}", "N", "Time (us)", "Melem/s", "Iters");
    println!("{:>8} {:>12} {:>12} {:>10}", "--------", "----------", "---------", "-----");
    for &(n, iters) in sizes {
        let twiddles = compute_bowers_twiddles(n, 7);
        let original: Vec<u64> = (0..n).map(|i| ((i as u128 * 1000000007) % p) as u64).collect();
        let mut warmup = original.clone();
        ntt_bowers(&mut warmup, &twiddles);
        std::hint::black_box(&warmup);
        let start = Instant::now();
        for _ in 0..iters {
            let mut data = original.clone();
            ntt_bowers(&mut data, &twiddles);
            std::hint::black_box(&data);
        }
        let elapsed = start.elapsed();
        let us = elapsed.as_secs_f64() / iters as f64 * 1e6;
        let melem = n as f64 / (us / 1e6) / 1e6;
        println!("{:>8} {:>12.0} {:>12.1} {:>10}", n, us, melem, iters);
    }
    println!();
    println!("Notes:");
    println!("  - Twiddle precomputation NOT included in timing");
    println!("  - Each iteration: clone (memcpy) + NTT in-place");
    println!("  - Warmup run before measurement");
}
