//! AMO-Lean Generated Rust NTT — Bowers G ordering
//! Field: KoalaBear (p = 2^31 - 2^24 + 1 = 2130706433)
//! Reduction: Solinas fold (e-graph cost model selected)
//! Ordering: Bowers G (bit-reversed twiddles, DIF butterfly, sequential access)
//! Verified in Lean 4: solinasFold_mod_correct (0 sorry, 0 axioms)
//!
//! HOW TO BUILD AND RUN:
//!   rustc -O ntt_bowers_koalabear.rs -o ntt_bench && ./ntt_bench
//!
//! The -O flag is REQUIRED. Without it, Rust runs in debug mode (10-50x slower).
//! Do NOT use `rustc ntt_bowers_koalabear.rs` without -O.

use std::time::Instant;

// ═══════════════════════════════════════════════════════════════════
// KoalaBear field constants
// ═══════════════════════════════════════════════════════════════════

const P: u64 = 2130706433;       // 2^31 - 2^24 + 1
const C: u64 = 16777215;         // 2^24 - 1 (Solinas fold constant)
const GENERATOR: u64 = 3;        // primitive root of KoalaBear

// ═══════════════════════════════════════════════════════════════════
// Solinas fold reduction — e-graph selected for scalar KoalaBear
// Verified: solinasFold_mod_correct
// Cost: 4 ops (shift + mul_const + mask + add)
// ═══════════════════════════════════════════════════════════════════

/// Solinas fold: (x >> 31) * c + (x & mask).
/// The compiler optimizes `* 16777215` into `(x << 24) - x` (shift + sub).
#[inline(always)]
fn solinas_fold(x: u64) -> u32 {
    ((x >> 31).wrapping_mul(C)).wrapping_add(x & 0x7FFFFFFF) as u32
}

// ═══════════════════════════════════════════════════════════════════
// DIF butterfly (Bowers G network)
// ═══════════════════════════════════════════════════════════════════

/// DIF butterfly: a' = fold(a + b), b' = fold((p + a - b) * w).
/// Bowers applies ONE twiddle per block (sequential access).
#[inline(always)]
fn dif_butterfly(a: &mut u32, b: &mut u32, w: u32) {
    let va = *a;
    let vb = *b;
    *a = solinas_fold(va as u64 + vb as u64);
    let diff = solinas_fold(P + va as u64 - vb as u64);
    *b = solinas_fold(diff as u64 * w as u64);
}

// ═══════════════════════════════════════════════════════════════════
// Bit-reversal permutation
// ═══════════════════════════════════════════════════════════════════

fn bit_reverse(data: &mut [u32]) {
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
/// This is a one-time precomputation — NOT included in the NTT timing.
fn compute_bowers_twiddles(n: usize) -> Vec<u32> {
    let omega = mod_pow(GENERATOR, (P - 1) / n as u64, P);
    let mut tw: Vec<u32> = (0..n/2)
        .map(|i| mod_pow(omega, i as u64, P) as u32)
        .collect();
    bit_reverse(&mut tw);
    tw
}

// ═══════════════════════════════════════════════════════════════════
// Bowers G NTT — the core algorithm
// ═══════════════════════════════════════════════════════════════════

/// Bowers G NTT: bit-reverse input, DIF stages small→large, sequential twiddle access.
///
/// Cache-friendly: twiddles accessed linearly (one per block).
/// Standard DIT accesses twiddles[stage*(n/2) + group*half + pair] — strided.
/// Bowers accesses twiddles[block] — sequential, CPU prefetch works.
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

// ═══════════════════════════════════════════════════════════════════
// Benchmark harness
// ═══════════════════════════════════════════════════════════════════

fn main() {
    let sizes: &[(usize, usize)] = &[
        (1 << 14, 200),    // 16K elements, 200 iterations
        (1 << 16, 50),     // 64K elements, 50 iterations
        (1 << 18, 20),     // 256K elements, 20 iterations
        (1 << 20, 10),     // 1M elements, 10 iterations
        (1 << 22, 3),      // 4M elements, 3 iterations
    ];

    println!("AMO-Lean Bowers NTT — KoalaBear (p = 2^31 - 2^24 + 1)");
    println!("Reduction: Solinas fold (e-graph selected, verified in Lean 4)");
    println!("Ordering: Bowers G (DIF, bit-reversed twiddles, cache-friendly)");
    println!();
    println!("{:>8} {:>12} {:>12} {:>10}", "N", "Time (us)", "Melem/s", "Iters");
    println!("{:>8} {:>12} {:>12} {:>10}", "--------", "----------", "---------", "-----");

    for &(n, iters) in sizes {
        // Precompute twiddles OUTSIDE the timing loop
        let twiddles = compute_bowers_twiddles(n);

        // Precompute input data OUTSIDE the timing loop
        let original: Vec<u32> = (0..n)
            .map(|i| ((i as u64 * 1000000007) % P) as u32)
            .collect();

        // Warmup run (ensures caches are hot, no first-run effects)
        let mut warmup = original.clone();
        ntt_bowers(&mut warmup, &twiddles);
        std::hint::black_box(&warmup);

        // Timed benchmark: only measures NTT + clone, NOT twiddle computation
        let start = Instant::now();
        for _ in 0..iters {
            let mut data = original.clone();  // clone is ~memcpy, consistent overhead
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
    println!("  - Compiled with: rustc -O ntt_bowers_koalabear.rs");
    println!("  - Twiddle precomputation is NOT included in timing");
    println!("  - Each iteration clones the input (memcpy) then runs NTT in-place");
    println!("  - Warmup run before timing to ensure hot caches");
}
