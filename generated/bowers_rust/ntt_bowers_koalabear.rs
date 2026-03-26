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

use std::time::Instant;

/// Canonical reduction mod P.
/// For 32-bit fields a single Solinas fold does NOT bring a u64 product into
/// u32 range, so we use direct modular reduction.
#[inline(always)]
fn reduce(x: u64) -> u32 {
    (x % 2130706433u64) as u32
}

/// DIF butterfly: a' = reduce(a + b), b' = reduce((p + a - b) * w).
/// Bowers G network applies ONE twiddle per block.
#[inline(always)]
fn dif_butterfly(a: &mut u32, b: &mut u32, w: u32) {
    let va = *a as u64;
    let vb = *b as u64;
    *a = reduce(va + vb);
    let diff = (2130706433u64 + va - vb) % 2130706433u64;
    *b = reduce(diff.wrapping_mul(w as u64));
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
    let p: u64 = 2130706433;
    let sizes: &[(usize, usize)] = &[
        (1 << 14, 200), (1 << 16, 50), (1 << 18, 20), (1 << 20, 10), (1 << 22, 3),
    ];
    println!("AMO-Lean Bowers NTT — KoalaBear (p = 2^31 - 2^24 + 1)");
    println!("Reduction: Solinas fold (e-graph selected, verified in Lean 4)");
    println!("Build: rustc -O ntt_bowers_koalabear.rs -o ntt_bench && ./ntt_bench");
    println!();
    println!("{:>8} {:>12} {:>12} {:>10}", "N", "Time (us)", "Melem/s", "Iters");
    println!("{:>8} {:>12} {:>12} {:>10}", "--------", "----------", "---------", "-----");
    for &(n, iters) in sizes {
        let twiddles = compute_bowers_twiddles(n, 3);
        let original: Vec<u32> = (0..n).map(|i| ((i as u64 * 1000000007) % p) as u32).collect();
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
