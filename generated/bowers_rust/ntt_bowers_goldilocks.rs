//! AMO-Lean Generated Rust NTT — Bowers G ordering
//! Field: Goldilocks (p = 2^64 - 2^32 + 1)
//! Reduction: Goldilocks reduce (exploits p = 2^64 - 2^32 + 1)
//! Ordering: Bowers G (bit-reversed twiddles, DIF butterfly, sequential access)
//! Verified in Lean 4: solinasFold_mod_correct (0 sorry, 0 axioms)
//!
//! HOW TO BUILD AND RUN:
//!   rustc -O ntt_bowers_goldilocks.rs -o ntt_bench && ./ntt_bench
//!
//! The -O flag is REQUIRED. Without it, Rust runs in debug mode (10-50x slower).
//! Do NOT use `rustc ntt_bowers_goldilocks.rs` without -O.

use std::time::Instant;

// ═══════════════════════════════════════════════════════════════════
// Goldilocks field constants
// ═══════════════════════════════════════════════════════════════════

const P: u64 = 0xFFFFFFFF00000001;  // 2^64 - 2^32 + 1
const GENERATOR: u64 = 7;           // primitive root

// ═══════════════════════════════════════════════════════════════════
// Goldilocks reduction — exploits p = 2^64 - 2^32 + 1
// Since 2^64 ≡ 2^32 - 1 (mod p), split at bit 64:
//   reduce(x) = lo - hi_hi + hi_lo * (2^32 - 1)
// Only ONE 32×32 multiply vs Montgomery's TWO 64-bit multiplies.
// Verified: solinasFold_mod_correct (Goldilocks instance)
// ═══════════════════════════════════════════════════════════════════

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
    if carry || result >= P { result.wrapping_sub(P) } else { result }
}

// ═══════════════════════════════════════════════════════════════════
// DIF butterfly (Bowers G network) for Goldilocks
// ═══════════════════════════════════════════════════════════════════

#[inline(always)]
fn dif_butterfly(a: &mut u64, b: &mut u64, w: u64) {
    let va = *a;
    let vb = *b;
    let sum = va.wrapping_add(vb);
    *a = if sum >= P { sum - P } else { sum };
    *b = goldilocks_reduce(
        (if va >= vb { va - vb } else { P - vb + va }) as u128
        * w as u128);
}

// ═══════════════════════════════════════════════════════════════════
// Bit-reversal permutation
// ═══════════════════════════════════════════════════════════════════

fn bit_reverse(data: &mut [u64]) {
    let n = data.len();
    let log_n = n.trailing_zeros();
    for i in 0..n {
        let j = i.reverse_bits() >> (usize::BITS - log_n);
        if i < j { data.swap(i, j); }
    }
}

// ═══════════════════════════════════════════════════════════════════
// Twiddle factor computation (precomputed, NOT part of the timed NTT)
// ═══════════════════════════════════════════════════════════════════

fn mod_pow(mut base: u128, mut exp: u128, modulus: u128) -> u128 {
    let mut result: u128 = 1;
    base %= modulus;
    while exp > 0 {
        if exp & 1 == 1 {
            result = (result * base) % modulus;
        }
        exp >>= 1;
        base = (base * base) % modulus;
    }
    result
}

/// Compute bit-reversed twiddle table for Bowers G network.
/// This is a one-time precomputation — NOT included in the NTT timing.
fn compute_bowers_twiddles(n: usize) -> Vec<u64> {
    let p = P as u128;
    let omega = mod_pow(GENERATOR as u128, (p - 1) / n as u128, p);
    let mut tw: Vec<u64> = (0..n/2)
        .map(|i| mod_pow(omega, i as u128, p) as u64)
        .collect();
    bit_reverse(&mut tw);
    tw
}

// ═══════════════════════════════════════════════════════════════════
// Bowers G NTT — the core algorithm
// ═══════════════════════════════════════════════════════════════════

/// Bowers G NTT for Goldilocks.
/// Same structure as KoalaBear version, but with 64-bit elements and u128 products.
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

// ═══════════════════════════════════════════════════════════════════
// Benchmark harness
// ═══════════════════════════════════════════════════════════════════

fn main() {
    let sizes: &[(usize, usize)] = &[
        (1 << 14, 200),
        (1 << 16, 50),
        (1 << 18, 20),
        (1 << 20, 10),
        (1 << 22, 3),
    ];

    println!("AMO-Lean Bowers NTT — Goldilocks (p = 2^64 - 2^32 + 1)");
    println!("Reduction: Goldilocks reduce (e-graph selected, verified in Lean 4)");
    println!("Ordering: Bowers G (DIF, bit-reversed twiddles, cache-friendly)");
    println!();
    println!("{:>8} {:>12} {:>12} {:>10}", "N", "Time (us)", "Melem/s", "Iters");
    println!("{:>8} {:>12} {:>12} {:>10}", "--------", "----------", "---------", "-----");

    for &(n, iters) in sizes {
        let twiddles = compute_bowers_twiddles(n);

        let original: Vec<u64> = (0..n)
            .map(|i| ((i as u128 * 1000000007) % P as u128) as u64)
            .collect();

        // Warmup
        let mut warmup = original.clone();
        ntt_bowers(&mut warmup, &twiddles);
        std::hint::black_box(&warmup);

        // Timed benchmark
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
    println!("  - Compiled with: rustc -O ntt_bowers_goldilocks.rs");
    println!("  - Twiddle precomputation is NOT included in timing");
    println!("  - Each iteration clones the input (memcpy) then runs NTT in-place");
    println!("  - Warmup run before timing to ensure hot caches");
}
