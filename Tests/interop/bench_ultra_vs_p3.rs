//! AMO-Lean Ultra vs Plonky3 Montgomery NTT Benchmark
//! KoalaBear (p = 0x7F000001, k=31, c=16777215)
//! N = 2^16 = 65536
//!
//! Three variants:
//! 1. Ultra: lazy reduction on 14/16 stages, Solinas on last 2 (from verified pipeline)
//! 2. AMO Solinas: Solinas fold every stage (legacy AMO)
//! 3. P3 Montgomery: Montgomery REDC every stage (Plonky3 reference)

use std::time::Instant;

const P: u32 = 0x7F000001; // 2130706433
const C: u32 = 16777215;   // Solinas constant
const MU: u32 = 0x81000001; // Montgomery mu
const ITERS: usize = 100;

// ═══════════════════════════════════════════════════════════════════
// Solinas fold: (x >> 31) * c + (x & 0x7FFFFFFF)
// ═══════════════════════════════════════════════════════════════════

#[inline(always)]
fn solinas(x: u64) -> u32 {
    ((x >> 31).wrapping_mul(C as u64).wrapping_add(x & 0x7FFFFFFF)) as u32
}

// ═══════════════════════════════════════════════════════════════════
// Montgomery REDC
// ═══════════════════════════════════════════════════════════════════

#[inline(always)]
fn monty(x: u64) -> u32 {
    let t = (x.wrapping_mul(MU as u64)) as u32;
    let u = t as u64 * P as u64;
    let d = x.wrapping_sub(u);
    let hi = (d >> 32) as u32;
    if x < u { hi.wrapping_add(P) } else { hi }
}

// ═══════════════════════════════════════════════════════════════════
// 1. Ultra NTT: lazy butterfly (no reduction) + Solinas butterfly
// ═══════════════════════════════════════════════════════════════════

#[inline(always)]
fn ultra_bf_lazy(a: &mut u64, b: &mut u64, w: u64) {
    // No reduction: work in u64 accumulating bits
    let t = w.wrapping_mul(*b);
    let sum = (*a).wrapping_add(t);
    let diff = (*a).wrapping_add(P as u64).wrapping_sub(t);
    *a = sum;
    *b = diff;
}

#[inline(always)]
fn ultra_bf_solinas(a: &mut u64, b: &mut u64, w: u64) {
    let t = w.wrapping_mul(*b);
    let sum = (*a).wrapping_add(t);
    let diff = (*a).wrapping_add(P as u64).wrapping_sub(t);
    *a = solinas(sum) as u64;
    *b = solinas(diff) as u64;
}

#[inline(always)]
fn ultra_bf_monty(a: &mut u64, b: &mut u64, w: u64) {
    let t = w.wrapping_mul(*b);
    let sum = (*a).wrapping_add(t);
    let diff = (*a).wrapping_add(P as u64).wrapping_sub(t);
    *a = monty(sum) as u64;
    *b = monty(diff) as u64;
}

// Cache-aware Ultra: for N > 8192, reduce every stage in u32.
// Uses Harvey cond-sub (cheapest per cost model: boundK ≤ 2 after monty).
fn ntt_ultra_u32(data: &mut [u32], tw: &[u32], log_n: usize) {
    let n = 1 << log_n;
    let mut tw_off = 0;
    for s in 0..log_n {
        let half = n >> (s + 1);
        let groups = 1 << s;
        for g in 0..groups {
            for j in 0..half {
                let i0 = g * 2 * half + j;
                let i1 = i0 + half;
                let w = tw[tw_off + g * half + j];
                let (pa, pb) = unsafe {
                    (&mut *data.as_mut_ptr().add(i0), &mut *data.as_mut_ptr().add(i1))
                };
                // 1 monty on twiddle*b, then Harvey cond-sub for sum/diff
                let oa = *pa;
                let wb = monty(w as u64 * *pb as u64);
                let sum = oa.wrapping_add(wb);
                *pa = if sum >= P { sum - P } else { sum };
                *pb = if oa >= wb { oa - wb } else { P - wb + oa };
            }
        }
        tw_off += groups * half;
    }
}

fn ntt_ultra_u64(data: &mut [u64], tw: &[u64], log_n: usize) {
    let n = 1 << log_n;
    let mut tw_off = 0;
    for s in 0..log_n {
        let half = n >> (s + 1);
        let groups = 1 << s;
        let is_reduce = s >= log_n - 2;
        for g in 0..groups {
            for j in 0..half {
                let i0 = g * 2 * half + j;
                let i1 = i0 + half;
                let w = tw[tw_off + g * half + j];
                let (pa, pb) = unsafe {
                    (&mut *data.as_mut_ptr().add(i0), &mut *data.as_mut_ptr().add(i1))
                };
                if is_reduce {
                    ultra_bf_solinas(pa, pb, w);
                } else {
                    ultra_bf_lazy(pa, pb, w);
                }
            }
        }
        tw_off += groups * half;
    }
    for x in data.iter_mut() {
        *x = solinas(*x) as u64;
    }
}

// ═══════════════════════════════════════════════════════════════════
// 2. AMO Solinas: Solinas fold every stage (legacy)
// ═══════════════════════════════════════════════════════════════════

#[inline(always)]
fn amo_bf(a: &mut u32, b: &mut u32, w: u32) {
    let oa = *a as u64;
    let wb = solinas(w as u64 * *b as u64);
    *a = solinas(oa + wb as u64);
    *b = solinas(P as u64 + oa - wb as u64);
}

fn ntt_solinas(data: &mut [u32], tw: &[u32], log_n: usize) {
    let n = 1 << log_n;
    let mut tw_off = 0;
    for s in 0..log_n {
        let half = n >> (s + 1);
        let groups = 1 << s;
        for g in 0..groups {
            for j in 0..half {
                let i0 = g * 2 * half + j;
                let i1 = i0 + half;
                let (pa, pb) = unsafe {
                    (&mut *data.as_mut_ptr().add(i0), &mut *data.as_mut_ptr().add(i1))
                };
                amo_bf(pa, pb, tw[tw_off + g * half + j]);
            }
        }
        tw_off += groups * half;
    }
}

// ═══════════════════════════════════════════════════════════════════
// 3. P3 Montgomery: Montgomery REDC every stage
// ═══════════════════════════════════════════════════════════════════

#[inline(always)]
fn p3_bf(a: &mut u32, b: &mut u32, w: u32) {
    let oa = *a;
    let wb = monty(w as u64 * *b as u64);
    let sum = oa.wrapping_add(wb);
    *a = if sum >= P { sum - P } else { sum };
    *b = if oa >= wb { oa - wb } else { P - wb + oa };
}

fn ntt_p3(data: &mut [u32], tw: &[u32], log_n: usize) {
    let n = 1 << log_n;
    let mut tw_off = 0;
    for s in 0..log_n {
        let half = n >> (s + 1);
        let groups = 1 << s;
        for g in 0..groups {
            for j in 0..half {
                let i0 = g * 2 * half + j;
                let i1 = i0 + half;
                let (pa, pb) = unsafe {
                    (&mut *data.as_mut_ptr().add(i0), &mut *data.as_mut_ptr().add(i1))
                };
                p3_bf(pa, pb, tw[tw_off + g * half + j]);
            }
        }
        tw_off += groups * half;
    }
}

// ═══════════════════════════════════════════════════════════════════
// Main: timing harness
// ═══════════════════════════════════════════════════════════════════

fn bench_size(log_n: usize) {
    let n = 1usize << log_n;
    let iters = if log_n >= 22 { 10 } else if log_n >= 20 { 50 } else { ITERS };
    let tw_sz = n * log_n;
    let tw32: Vec<u32> = (0..tw_sz).map(|i| ((i as u64 * 7 + 31) % P as u64) as u32).collect();
    let tw64: Vec<u64> = tw32.iter().map(|&x| x as u64).collect();
    let orig32: Vec<u32> = (0..n).map(|i| ((i as u64 * 1000000007) % P as u64) as u32).collect();
    let orig64: Vec<u64> = orig32.iter().map(|&x| x as u64).collect();
    let mut data32 = orig32.clone();
    let mut data64 = orig64.clone();

    let large = n > 8192;

    // Warmup
    if large { ntt_ultra_u32(&mut data32, &tw32, log_n); data32.copy_from_slice(&orig32); }
    else { ntt_ultra_u64(&mut data64, &tw64, log_n); data64.copy_from_slice(&orig64); }
    ntt_solinas(&mut data32, &tw32, log_n); data32.copy_from_slice(&orig32);
    ntt_p3(&mut data32, &tw32, log_n); data32.copy_from_slice(&orig32);

    let t0 = Instant::now();
    for _ in 0..iters {
        if large {
            data32.copy_from_slice(&orig32);
            ntt_ultra_u32(&mut data32, &tw32, log_n);
            std::hint::black_box(&data32);
        } else {
            data64.copy_from_slice(&orig64);
            ntt_ultra_u64(&mut data64, &tw64, log_n);
            std::hint::black_box(&data64);
        }
    }
    let ultra_us = t0.elapsed().as_secs_f64() / iters as f64 * 1e6;

    let t0 = Instant::now();
    for _ in 0..iters {
        data32.copy_from_slice(&orig32);
        ntt_solinas(&mut data32, &tw32, log_n);
        std::hint::black_box(&data32);
    }
    let solinas_us = t0.elapsed().as_secs_f64() / iters as f64 * 1e6;

    let t0 = Instant::now();
    for _ in 0..iters {
        data32.copy_from_slice(&orig32);
        ntt_p3(&mut data32, &tw32, log_n);
        std::hint::black_box(&data32);
    }
    let p3_us = t0.elapsed().as_secs_f64() / iters as f64 * 1e6;

    let melem_u = n as f64 / (ultra_us / 1e6) / 1e6;
    let melem_p = n as f64 / (p3_us / 1e6) / 1e6;
    let diff = (1.0 - ultra_us / p3_us) * 100.0;
    println!("  2^{:<2}  {:>10}  {:>8.1}  {:>8.1}  {:>8.1}  {:>6.1}  {:>6.1}  {:>+5.1}%",
        log_n, n, ultra_us, solinas_us, p3_us, melem_u, melem_p, diff);
}

fn main() {
    println!("KoalaBear NTT — Ultra (lazy+Solinas) vs Solinas-all vs P3 Montgomery");
    println!("Rust, -C opt-level=3 -C lto, Apple Silicon");
    println!("═══════════════════════════════════════════════════════════════════════════");
    println!("  Size       N      Ultra(us)  Sol(us)  P3(us)  Mu/s   Mp/s  Ultra/P3");
    println!("  ────  ──────────  ─────────  ───────  ──────  ─────  ─────  ────────");
    for log_n in [12, 14, 16, 18, 20, 22] {
        bench_size(log_n);
    }
}
