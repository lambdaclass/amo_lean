//! FIELD ARITHMETIC BENCHMARK: AMO-Lean reduce vs Plonky3 field ops
//!
//! Measures the raw cost of field multiplication (which includes reduction)
//! for each field, comparing AMO-Lean's Solinas fold against Plonky3's
//! Montgomery REDC. This isolates the reduction unit — no NTT structure.
//!
//! Run: cd tests/interop/bench_field_arith && rustup run nightly cargo run --release

use std::time::Instant;

use p3_baby_bear::BabyBear;
use p3_koala_bear::KoalaBear;
use p3_goldilocks::Goldilocks;
use p3_field::PrimeCharacteristicRing;

// ═══════════════════════════════════════════════════════════════════
// AMO-Lean: Solinas fold reductions (e-graph selected for scalar)
// ═══════════════════════════════════════════════════════════════════

#[inline(always)]
fn bb_reduce(x: u64) -> u32 {
    ((x >> 31).wrapping_mul(134217727).wrapping_add(x & 0x7FFFFFFF)) as u32
}

#[inline(always)]
fn kb_reduce(x: u64) -> u32 {
    ((x >> 31).wrapping_mul(16777215).wrapping_add(x & 0x7FFFFFFF)) as u32
}

#[inline(always)]
fn gl_reduce(x: u128) -> u64 {
    let lo = x as u64;
    let hi = (x >> 64) as u64;
    let hh = hi >> 32;
    let hl = hi & 0xFFFFFFFF;
    let (t0, borrow) = lo.overflowing_sub(hh);
    let t0 = if borrow { t0.wrapping_sub(0xFFFFFFFF) } else { t0 };
    let t1 = hl.wrapping_mul(0xFFFFFFFF);
    let (r, carry) = t0.overflowing_add(t1);
    if carry || r >= 0xFFFFFFFF00000001 { r.wrapping_sub(0xFFFFFFFF00000001) } else { r }
}

// ═══════════════════════════════════════════════════════════════════
// Benchmarks
// ═══════════════════════════════════════════════════════════════════

fn bench_mul_u32<F: p3_field::Field + PrimeCharacteristicRing + Copy>(
    name: &str,
    reduce: fn(u64) -> u32,
    n: usize,
    iters: usize,
) {
    let p3_a: Vec<F> = (0..n).map(|i| F::from_u32((i as u32).wrapping_mul(1000000007))).collect();
    let p3_b: Vec<F> = (0..n).map(|i| F::from_u32((i as u32).wrapping_mul(999999937))).collect();

    let amo_a: Vec<u32> = (0..n).map(|i| (i as u32).wrapping_mul(1000000007)).collect();
    let amo_b: Vec<u32> = (0..n).map(|i| (i as u32).wrapping_mul(999999937)).collect();

    // Plonky3 field multiply (Montgomery)
    let start = Instant::now();
    for _ in 0..iters {
        let mut acc = F::ONE;
        for i in 0..n {
            acc = acc * p3_a[i] * p3_b[i];
        }
        std::hint::black_box(acc);
    }
    let p3_us = start.elapsed().as_secs_f64() / iters as f64 * 1e6;

    // AMO-Lean Solinas fold multiply
    let start = Instant::now();
    for _ in 0..iters {
        let mut acc: u32 = 1;
        for i in 0..n {
            acc = reduce(acc as u64 * amo_a[i] as u64);
            acc = reduce(acc as u64 * amo_b[i] as u64);
        }
        std::hint::black_box(acc);
    }
    let amo_us = start.elapsed().as_secs_f64() / iters as f64 * 1e6;

    let mops = n as f64 * 2.0 * iters as f64 / (amo_us / 1e6) / 1e6;
    let diff = (1.0 - amo_us / p3_us) * 100.0;
    println!("{},{},mul,{:.0},{:.0},{:.0},{:+.1}",
        name, n, amo_us, p3_us, mops, diff);
}

fn bench_mul_goldilocks(n: usize, iters: usize) {
    let p3_a: Vec<Goldilocks> = (0..n).map(|i| Goldilocks::from_u64(i as u64 * 1000000007)).collect();
    let p3_b: Vec<Goldilocks> = (0..n).map(|i| Goldilocks::from_u64(i as u64 * 999999937)).collect();

    let amo_a: Vec<u64> = (0..n).map(|i| i as u64 * 1000000007).collect();
    let amo_b: Vec<u64> = (0..n).map(|i| i as u64 * 999999937).collect();

    let start = Instant::now();
    for _ in 0..iters {
        let mut acc = Goldilocks::ONE;
        for i in 0..n {
            acc = acc * p3_a[i] * p3_b[i];
        }
        std::hint::black_box(acc);
    }
    let p3_us = start.elapsed().as_secs_f64() / iters as f64 * 1e6;

    let start = Instant::now();
    for _ in 0..iters {
        let mut acc: u64 = 1;
        for i in 0..n {
            acc = gl_reduce(acc as u128 * amo_a[i] as u128);
            acc = gl_reduce(acc as u128 * amo_b[i] as u128);
        }
        std::hint::black_box(acc);
    }
    let amo_us = start.elapsed().as_secs_f64() / iters as f64 * 1e6;

    let mops = n as f64 * 2.0 * iters as f64 / (amo_us / 1e6) / 1e6;
    let diff = (1.0 - amo_us / p3_us) * 100.0;
    println!("Goldilocks,{},mul,{:.0},{:.0},{:.0},{:+.1}",
        n, amo_us, p3_us, mops, diff);
}

fn main() {
    println!("field,n,op,amo_us,p3_us,mops,diff_pct");
    println!("# Field arithmetic: AMO-Lean Solinas vs Plonky3 Montgomery");
    println!("# Measures raw field multiply throughput (includes reduction)");
    println!("# Both native Rust, --release LTO, same binary");

    let sizes = [10_000, 100_000, 1_000_000];
    let iters_for = |n: usize| if n <= 10_000 { 1000 } else if n <= 100_000 { 100 } else { 10 };

    for &n in &sizes {
        bench_mul_u32::<BabyBear>("BabyBear", bb_reduce, n, iters_for(n));
    }
    for &n in &sizes {
        bench_mul_u32::<KoalaBear>("KoalaBear", kb_reduce, n, iters_for(n));
    }
    for &n in &sizes {
        bench_mul_goldilocks(n, iters_for(n));
    }
}
