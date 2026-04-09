//! BOWERS FFT BENCHMARK: AMO-Lean Bowers vs Plonky3 Radix2Bowers
//!
//! Both use Bowers G network (bit-reversed twiddles, DIF butterfly, small→large stages).
//! AMO-Lean uses Solinas fold for reduction. Plonky3 uses Montgomery REDC.
//! Plonky3 called via its native API (Radix2Bowers::dft_batch).
//!
//! Fields: KoalaBear, Goldilocks (as requested)
//! Sizes: production (2^14 to 2^22)

use std::time::Instant;

use p3_baby_bear::BabyBear;
use p3_koala_bear::KoalaBear;
use p3_goldilocks::Goldilocks;
use p3_dft::{Radix2Bowers, TwoAdicSubgroupDft};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use rand::SeedableRng;
use rand::RngCore;
use rand::rngs::SmallRng;

// ═══════════════════════════════════════════════════════════════════
// AMO-Lean Bowers NTT: Solinas fold + DIF butterfly + Bowers ordering
// ═══════════════════════════════════════════════════════════════════

const BB_P: u32 = 0x78000001;  // BabyBear
const BB_C: u32 = 134217727;   // 2^27 - 1
const KB_P: u32 = 0x7F000001;  // KoalaBear
const KB_C: u32 = 16777215;    // 2^24 - 1
const M31_P: u32 = 0x7FFFFFFF; // Mersenne31
const M31_C: u32 = 1;          // 2^1 - 1

const GL_P: u64 = 0xFFFFFFFF00000001;

/// Solinas fold for 31-bit primes.
#[inline(always)]
fn solinas(x: u64, c: u32) -> u32 {
    ((x >> 31).wrapping_mul(c as u64).wrapping_add(x & 0x7FFFFFFF)) as u32
}

/// Goldilocks reduction (64-bit prime, needs u128).
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
    if carry || r >= GL_P { r.wrapping_sub(GL_P) } else { r }
}

/// Bit-reversal permutation.
fn bit_reverse<T: Copy>(data: &mut [T]) {
    let n = data.len();
    let log_n = n.trailing_zeros();
    for i in 0..n {
        let j = i.reverse_bits() >> (usize::BITS - log_n);
        if i < j {
            data.swap(i, j);
        }
    }
}

/// Modular exponentiation for twiddle computation.
fn mod_pow_u64(mut base: u64, mut exp: u64, modulus: u64) -> u64 {
    let mut result = 1u64;
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

/// Compute bit-reversed twiddle table for Bowers G network (DIF).
/// twiddles[i] = omega^(bit_reverse(i)) for i in 0..n/2
fn compute_bowers_twiddles_u32(n: usize, p: u64, generator: u64) -> Vec<u32> {
    let half = n / 2;
    let omega = mod_pow_u64(generator, (p - 1) / n as u64, p);
    let mut tw: Vec<u32> = (0..half)
        .map(|i| mod_pow_u64(omega, i as u64, p) as u32)
        .collect();
    bit_reverse(&mut tw);
    tw
}

fn compute_bowers_twiddles_u64(n: usize, p: u64, generator: u64) -> Vec<u64> {
    let half = n / 2;
    let omega = mod_pow_u64(generator, (p - 1) / n as u64, p);
    let mut tw: Vec<u64> = (0..half)
        .map(|i| mod_pow_u64(omega, i as u64, p))
        .collect();
    bit_reverse(&mut tw);
    tw
}

/// AMO-Lean Bowers NTT for any 31-bit Solinas prime.
fn amo_bowers_u32(data: &mut [u32], twiddles_br: &[u32], p: u32, c: u32) {
    let n = data.len();
    let log_n = n.trailing_zeros() as usize;
    bit_reverse(data);
    for log_half in 0..log_n {
        let half = 1usize << log_half;
        let block_size = 2 * half;
        let num_blocks = n / block_size;
        for block in 0..num_blocks {
            let w = if block == 0 { 1u32 } else { twiddles_br[block] };
            let base = block * block_size;
            for j in 0..half {
                let i0 = base + j;
                let i1 = i0 + half;
                let a = data[i0];
                let b = data[i1];
                data[i0] = solinas(a as u64 + b as u64, c);
                let diff = solinas(p as u64 + a as u64 - b as u64, c);
                data[i1] = solinas(diff as u64 * w as u64, c);
            }
        }
    }
}

/// Generic benchmark for any 31-bit field vs Plonky3 Bowers.
fn bench_u32_field<F: p3_field::TwoAdicField + PrimeCharacteristicRing>(
    name: &str, p: u32, c: u32, generator: u64, log_n: usize, iters: usize
) {
    let n = 1 << log_n;
    let twiddles = compute_bowers_twiddles_u32(n, p as u64, generator);
    let mut rng = SmallRng::seed_from_u64(42);
    let p3_data: Vec<F> = (0..n).map(|_| F::from_u32(rng.next_u32() % p)).collect();
    let dft = Radix2Bowers;
    let _ = dft.dft_batch(RowMajorMatrix::new_col(p3_data.clone()));
    let amo_data: Vec<u32> = (0..n).map(|i| ((i as u64 * 1000000007) % p as u64) as u32).collect();
    let mut warmup = amo_data.clone();
    amo_bowers_u32(&mut warmup, &twiddles, p, c);

    let start = Instant::now();
    for _ in 0..iters {
        let mat = RowMajorMatrix::new_col(p3_data.clone());
        let _ = std::hint::black_box(dft.dft_batch(mat));
    }
    let p3_us = start.elapsed().as_secs_f64() / iters as f64 * 1e6;

    let start = Instant::now();
    for _ in 0..iters {
        let mut data = amo_data.clone();
        amo_bowers_u32(&mut data, &twiddles, p, c);
        std::hint::black_box(&data);
    }
    let amo_us = start.elapsed().as_secs_f64() / iters as f64 * 1e6;

    let diff = (1.0 - amo_us / p3_us) * 100.0;
    println!("{},{},{},NTT-Bowers,{:.0},{:.0},{:+.1}", name, log_n, n, amo_us, p3_us, diff);
}

/// AMO-Lean Bowers NTT for KoalaBear (Solinas fold + DIF butterfly).
/// Bowers G: bit-reverse input, DIF stages small→large, sequential twiddle access.
fn amo_bowers_kb(data: &mut [u32], twiddles_br: &[u32]) {
    let n = data.len();
    let log_n = n.trailing_zeros() as usize;

    bit_reverse(data);

    for log_half in 0..log_n {
        let half = 1usize << log_half;
        let block_size = 2 * half;
        let num_blocks = n / block_size;

        for block in 0..num_blocks {
            let w = if block == 0 { 1u32 } else { twiddles_br[block] };
            let base = block * block_size;
            for j in 0..half {
                let i0 = base + j;
                let i1 = i0 + half;
                // DIF butterfly: a' = a + b, b' = (a - b) * w
                let a = data[i0];
                let b = data[i1];
                let sum = solinas(a as u64 + b as u64, KB_C);
                let diff = solinas(KB_P as u64 + a as u64 - b as u64, KB_C);
                data[i0] = sum;
                data[i1] = solinas(diff as u64 * w as u64, KB_C);
            }
        }
    }
}

/// AMO-Lean Bowers NTT for Goldilocks.
fn amo_bowers_gl(data: &mut [u64], twiddles_br: &[u64]) {
    let n = data.len();
    let log_n = n.trailing_zeros() as usize;

    bit_reverse(data);

    for log_half in 0..log_n {
        let half = 1usize << log_half;
        let block_size = 2 * half;
        let num_blocks = n / block_size;

        for block in 0..num_blocks {
            let w = if block == 0 { 1u64 } else { twiddles_br[block] };
            let base = block * block_size;
            for j in 0..half {
                let i0 = base + j;
                let i1 = i0 + half;
                let a = data[i0];
                let b = data[i1];
                let sum = { let s = a.wrapping_add(b); if s >= GL_P { s - GL_P } else { s } };
                let diff = if a >= b { a - b } else { GL_P - b + a };
                data[i0] = sum;
                data[i1] = gl_reduce(diff as u128 * w as u128);
            }
        }
    }
}

// ═══════════════════════════════════════════════════════════════════
// Benchmark
// ═══════════════════════════════════════════════════════════════════

fn bench_koalabear(log_n: usize, iters: usize) {
    let n = 1 << log_n;
    // KoalaBear generator: 3 is a primitive root
    let twiddles = compute_bowers_twiddles_u32(n, KB_P as u64, 3);

    let mut rng = SmallRng::seed_from_u64(42);
    let p3_data: Vec<KoalaBear> = (0..n)
        .map(|_| KoalaBear::from_u32(rng.next_u32() % KB_P))
        .collect();
    let dft = Radix2Bowers;

    // Warmup (caches twiddles)
    let _ = dft.dft_batch(RowMajorMatrix::new_col(p3_data.clone()));

    let amo_data: Vec<u32> = (0..n).map(|i| ((i as u64 * 1000000007) % KB_P as u64) as u32).collect();
    let mut warmup = amo_data.clone();
    amo_bowers_kb(&mut warmup, &twiddles);

    // Benchmark Plonky3 Bowers
    let start = Instant::now();
    for _ in 0..iters {
        let mat = RowMajorMatrix::new_col(p3_data.clone());
        let _ = std::hint::black_box(dft.dft_batch(mat));
    }
    let p3_us = start.elapsed().as_secs_f64() / iters as f64 * 1e6;

    // Benchmark AMO-Lean Bowers
    let start = Instant::now();
    for _ in 0..iters {
        let mut data = amo_data.clone();
        amo_bowers_kb(&mut data, &twiddles);
        std::hint::black_box(&data);
    }
    let amo_us = start.elapsed().as_secs_f64() / iters as f64 * 1e6;

    let diff = (1.0 - amo_us / p3_us) * 100.0;
    println!("KoalaBear,{},{},NTT-Bowers,{:.0},{:.0},{:+.1}",
        log_n, n, amo_us, p3_us, diff);
}

fn bench_goldilocks(log_n: usize, iters: usize) {
    let n = 1 << log_n;
    // Goldilocks generator: 7 is a primitive root
    let twiddles = compute_bowers_twiddles_u64(n, GL_P, 7);

    let mut rng = SmallRng::seed_from_u64(42);
    let p3_data: Vec<Goldilocks> = (0..n)
        .map(|_| Goldilocks::from_u64(rng.next_u64() % GL_P))
        .collect();
    let dft = Radix2Bowers;

    // Warmup
    let _ = dft.dft_batch(RowMajorMatrix::new_col(p3_data.clone()));

    let amo_data: Vec<u64> = (0..n).map(|i| (i as u64 * 1000000007) % GL_P).collect();
    let mut warmup = amo_data.clone();
    amo_bowers_gl(&mut warmup, &twiddles);

    // Benchmark Plonky3 Bowers
    let start = Instant::now();
    for _ in 0..iters {
        let mat = RowMajorMatrix::new_col(p3_data.clone());
        let _ = std::hint::black_box(dft.dft_batch(mat));
    }
    let p3_us = start.elapsed().as_secs_f64() / iters as f64 * 1e6;

    // Benchmark AMO-Lean Bowers
    let start = Instant::now();
    for _ in 0..iters {
        let mut data = amo_data.clone();
        amo_bowers_gl(&mut data, &twiddles);
        std::hint::black_box(&data);
    }
    let amo_us = start.elapsed().as_secs_f64() / iters as f64 * 1e6;

    let diff = (1.0 - amo_us / p3_us) * 100.0;
    println!("Goldilocks,{},{},NTT-Bowers,{:.0},{:.0},{:+.1}",
        log_n, n, amo_us, p3_us, diff);
}

fn main() {
    println!("field,log_n,n,primitive,amo_us,p3_us,diff_pct");
    println!("# AMO-Lean Bowers vs Plonky3 Radix2Bowers (native Rust API)");
    println!("# Both --release LTO, same binary. 4 fields × 5 sizes.");

    let sizes: [(usize, usize); 5] = [
        (14, 500),
        (16, 200),
        (18, 50),
        (20, 10),
        (22, 3),
    ];

    for &(log_n, iters) in &sizes {
        bench_u32_field::<BabyBear>("BabyBear", BB_P, BB_C, 31, log_n, iters);
    }
    for &(log_n, iters) in &sizes {
        bench_u32_field::<KoalaBear>("KoalaBear", KB_P, KB_C, 3, log_n, iters);
    }
    for &(log_n, iters) in &sizes {
        bench_goldilocks(log_n, iters);
    }
}
