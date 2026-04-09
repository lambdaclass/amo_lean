//! DEFINITIVE RUST BENCHMARK: AMO-Lean vs Plonky3-style Montgomery
//! 3 fields × 4 primitives × 6 sizes, same binary, --release
//! Mirrors the C benchmark exactly for cross-language comparison.
//!
//! Strategy (from cost model, solinasWinsForMulAdd = false):
//!   NTT:            Solinas fold butterfly (e-graph selected)
//!   Poly/FRI/Dot:   Montgomery+1br (cost-model selected, branch-aware)

use std::time::Instant;

// ═══════════════════════════════════════════════════════════════════
// Field definitions
// ═══════════════════════════════════════════════════════════════════

struct Field {
    name: &'static str,
    p: u32,
    c: u32,
    mu: u32,
}

const BABYBEAR: Field = Field { name: "BabyBear", p: 0x78000001, c: 134217727, mu: 0x88000001 };
const KOALABEAR: Field = Field { name: "KoalaBear", p: 0x7F000001, c: 16777215, mu: 0x81000001 };
const MERSENNE31: Field = Field { name: "Mersenne31", p: 0x7FFFFFFF, c: 1, mu: 0x7FFFFFFF };

// ═══════════════════════════════════════════════════════════════════
// AMO-Lean: Solinas fold (for NTT butterfly)
// ═══════════════════════════════════════════════════════════════════

#[inline(always)]
fn solinas(x: u64, c: u32) -> u32 {
    ((x >> 31).wrapping_mul(c as u64).wrapping_add(x & 0x7FFFFFFF)) as u32
}

#[inline(always)]
fn amo_butterfly(a: &mut u32, b: &mut u32, w: u32, p: u32, c: u32) {
    let oa = *a;
    let wb = solinas(w as u64 * *b as u64, c);
    *a = solinas(oa as u64 + wb as u64, c);
    *b = solinas(p as u64 + oa as u64 - wb as u64, c);
}

// ═══════════════════════════════════════════════════════════════════
// Montgomery REDC (used by both AMO cost-model and Plonky3)
// ═══════════════════════════════════════════════════════════════════

#[inline(always)]
fn monty(x: u64, p: u32, mu: u32) -> u32 {
    let t = x.wrapping_mul(mu as u64) as u32;
    let u = t as u64 * p as u64;
    let d = x.wrapping_sub(u);
    let hi = (d >> 32) as u32;
    if x < u { hi.wrapping_add(p) } else { hi }
}

#[inline(always)]
fn p3_butterfly(a: &mut u32, b: &mut u32, w: u32, p: u32, mu: u32) {
    let oa = *a;
    let wb = monty(w as u64 * *b as u64, p, mu);
    let sum = oa.wrapping_add(wb);
    *a = if sum >= p { sum - p } else { sum };
    *b = if oa >= wb { oa - wb } else { p - wb + oa };
}

// ═══════════════════════════════════════════════════════════════════
// Benchmark
// ═══════════════════════════════════════════════════════════════════

fn bench(f: &Field, n: usize, ntt_it: usize, lin_it: usize) {
    let log_n = (n as f64).log2() as usize;
    let tw_sz = n * log_n;
    let tw: Vec<u32> = (0..tw_sz).map(|i| ((i as u64 * 7 + 31) % f.p as u64) as u32).collect();
    let a_orig: Vec<u32> = (0..n).map(|i| ((i as u64 * 1000000007) % f.p as u64) as u32).collect();
    let b_orig: Vec<u32> = (0..n).map(|i| ((i as u64 * 999999937) % f.p as u64) as u32).collect();
    let coeffs: [u32; 8] = [42, 17, 99, 3, 55, 7, 13, 1];

    // --- NTT: AMO Solinas butterfly ---
    let start = Instant::now();
    for _ in 0..ntt_it {
        let mut d = a_orig.clone();
        for st in 0..log_n {
            let h = 1 << (log_n - st - 1);
            for g in 0..(1usize << st) {
                let mut p2 = 0;
                while p2 + 1 <= h {
                    let i = g * 2 * h + p2;
                    let j = i + h;
                    let w = tw[(st * (n / 2) + g * h + p2) % tw_sz];
                    let (left, right) = d.split_at_mut(j);
                    amo_butterfly(&mut left[i], &mut right[0], w, f.p, f.c);
                    p2 += 1;
                }
            }
        }
        std::hint::black_box(d[0]);
    }
    let a_ntt = start.elapsed().as_secs_f64() / ntt_it as f64 * 1e6;

    // --- NTT: P3 Montgomery butterfly ---
    let start = Instant::now();
    for _ in 0..ntt_it {
        let mut d = a_orig.clone();
        for st in 0..log_n {
            let h = 1 << (log_n - st - 1);
            for g in 0..(1usize << st) {
                let mut p2 = 0;
                while p2 + 1 <= h {
                    let i = g * 2 * h + p2;
                    let j = i + h;
                    let w = tw[(st * (n / 2) + g * h + p2) % tw_sz];
                    let (left, right) = d.split_at_mut(j);
                    p3_butterfly(&mut left[i], &mut right[0], w, f.p, f.mu);
                    p2 += 1;
                }
            }
        }
        std::hint::black_box(d[0]);
    }
    let p_ntt = start.elapsed().as_secs_f64() / ntt_it as f64 * 1e6;

    // --- Poly: AMO Montgomery+1br (cost-model) ---
    let start = Instant::now();
    for _ in 0..lin_it {
        for i in 0..n {
            let mut ac = coeffs[7];
            for j in (1..=7).rev() {
                ac = monty(a_orig[i] as u64 * ac as u64, f.p, f.mu);
                let sm = coeffs[j - 1].wrapping_add(ac);
                ac = if sm >= f.p { sm - f.p } else { sm };
            }
            std::hint::black_box(ac);
        }
    }
    let a_poly = start.elapsed().as_secs_f64() / lin_it as f64 * 1e6;

    // --- Poly: P3 Montgomery+1br ---
    let start = Instant::now();
    for _ in 0..lin_it {
        for i in 0..n {
            let mut ac = coeffs[7];
            for j in (1..=7).rev() {
                ac = monty(a_orig[i] as u64 * ac as u64, f.p, f.mu);
                let sm = coeffs[j - 1].wrapping_add(ac);
                ac = if sm >= f.p { sm - f.p } else { sm };
            }
            std::hint::black_box(ac);
        }
    }
    let p_poly = start.elapsed().as_secs_f64() / lin_it as f64 * 1e6;

    // --- FRI: AMO Montgomery+1br ---
    let mut r = vec![0u32; n];
    let start = Instant::now();
    for _ in 0..lin_it {
        for i in 0..n {
            let pr = monty(42u64 * b_orig[i] as u64, f.p, f.mu);
            let sm = a_orig[i].wrapping_add(pr);
            r[i] = if sm >= f.p { sm - f.p } else { sm };
        }
        std::hint::black_box(r[n / 2]);
    }
    let a_fri = start.elapsed().as_secs_f64() / lin_it as f64 * 1e6;

    // --- FRI: P3 Montgomery+1br ---
    let start = Instant::now();
    for _ in 0..lin_it {
        for i in 0..n {
            let pr = monty(42u64 * b_orig[i] as u64, f.p, f.mu);
            let sm = a_orig[i].wrapping_add(pr);
            r[i] = if sm >= f.p { sm - f.p } else { sm };
        }
        std::hint::black_box(r[n / 2]);
    }
    let p_fri = start.elapsed().as_secs_f64() / lin_it as f64 * 1e6;

    // --- Dot: AMO Montgomery+1br ---
    let start = Instant::now();
    for _ in 0..lin_it {
        let mut ac = 0u32;
        for i in 0..n {
            let pr = monty(a_orig[i] as u64 * b_orig[i] as u64, f.p, f.mu);
            let sm = ac.wrapping_add(pr);
            ac = if sm >= f.p { sm - f.p } else { sm };
        }
        std::hint::black_box(ac);
    }
    let a_dot = start.elapsed().as_secs_f64() / lin_it as f64 * 1e6;

    // --- Dot: P3 Montgomery+1br ---
    let start = Instant::now();
    for _ in 0..lin_it {
        let mut ac = 0u32;
        for i in 0..n {
            let pr = monty(a_orig[i] as u64 * b_orig[i] as u64, f.p, f.mu);
            let sm = ac.wrapping_add(pr);
            ac = if sm >= f.p { sm - f.p } else { sm };
        }
        std::hint::black_box(ac);
    }
    let p_dot = start.elapsed().as_secs_f64() / lin_it as f64 * 1e6;

    // CSV output
    println!("{},{},{},NTT,{:.1},{:.1},{:+.1},Solinas,Montgomery",
        f.name, log_n, n, a_ntt, p_ntt, (1.0 - a_ntt / p_ntt) * 100.0);
    println!("{},{},{},Poly,{:.1},{:.1},{:+.1},Montgomery+1br,Montgomery+1br",
        f.name, log_n, n, a_poly, p_poly, (1.0 - a_poly / p_poly) * 100.0);
    println!("{},{},{},FRI,{:.1},{:.1},{:+.1},Montgomery+1br,Montgomery+1br",
        f.name, log_n, n, a_fri, p_fri, (1.0 - a_fri / p_fri) * 100.0);
    println!("{},{},{},Dot,{:.1},{:.1},{:+.1},Montgomery+1br,Montgomery+1br",
        f.name, log_n, n, a_dot, p_dot, (1.0 - a_dot / p_dot) * 100.0);
}

fn main() {
    println!("field,log_n,n,primitive,amo_us,p3_us,diff_pct,amo_strategy,p3_strategy");

    let fields = [&BABYBEAR, &KOALABEAR, &MERSENNE31];
    let sizes: [(usize, usize, usize); 6] = [
        (1 << 12, 1000, 2000),
        (1 << 14, 500,  1000),
        (1 << 16, 200,  500),
        (1 << 18, 50,   100),
        (1 << 20, 10,   20),
        (1 << 22, 3,    5),
    ];

    for &(n, ntt_it, lin_it) in &sizes {
        for f in &fields {
            bench(f, n, ntt_it, lin_it);
        }
    }
}
