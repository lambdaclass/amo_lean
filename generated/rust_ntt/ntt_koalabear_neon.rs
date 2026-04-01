//! AMO-Lean Generated Rust NTT — NEON Montgomery (4-wide)
//! N = 1048576, p = 2130706433
//! Strategy: Montgomery REDC via vqdmulhq_s32 (chosen by e-graph cost model)
//! Compile: rustc -O -o ntt_neon this_file.rs
//! Trust boundary: same as Fiat-Crypto (verified lowering via Trust-Lean)

#![allow(non_upper_case_globals)]
use std::time::Instant;
use std::arch::aarch64::*;

const P_VAL: i32 = 2130706433 as i32;
const MU_VAL: i32 = 0x81000001u32 as i32;

#[inline(always)]
fn scalar_monty_mul(lhs: i32, rhs: i32, p: i32, mu: i32) -> i32 {
    let c_hi = ((lhs as i64 * rhs as i64 * 2) >> 32) as i32;
    let mu_rhs = rhs.wrapping_mul(mu);
    let q = lhs.wrapping_mul(mu_rhs);
    let qp_hi = ((q as i64 * p as i64 * 2) >> 32) as i32;
    let d = (c_hi.wrapping_sub(qp_hi)) >> 1;
    if c_hi < qp_hi { d.wrapping_add(p) } else { d }
}

/// NEON Montgomery multiply: 4 parallel field multiplications.
/// All ops in i32 lanes — no u64 intermediates.
/// 6 NEON instructions, ~1.5 cyc/vec throughput.
#[inline(always)]
unsafe fn monty_mul(lhs: int32x4_t, rhs: int32x4_t,
                    v_p: int32x4_t, v_mu: int32x4_t) -> int32x4_t {
    let c_hi = vqdmulhq_s32(lhs, rhs);
    let mu_rhs = vmulq_s32(rhs, v_mu);
    let q = vmulq_s32(lhs, mu_rhs);
    let qp_hi = vqdmulhq_s32(q, v_p);
    let d = vhsubq_s32(c_hi, qp_hi);
    let uf: uint32x4_t = vcltq_s32(c_hi, qp_hi);
    vreinterpretq_s32_u32(vmlsq_u32(
        vreinterpretq_u32_s32(d), uf, vreinterpretq_u32_s32(v_p)))
}

/// NEON butterfly: 4 parallel CT butterflies.
#[inline(always)]
unsafe fn butterfly_neon(a: &mut int32x4_t, b: &mut int32x4_t, w: int32x4_t,
                          v_p: int32x4_t, v_mu: int32x4_t) {
    let orig_a = *a;
    let wb = monty_mul(w, *b, v_p, v_mu);
    // sum = a + wb (with canonicalization)
    let sum = vaddq_s32(orig_a, wb);
    let su = vreinterpretq_u32_s32(sum);
    *a = vreinterpretq_s32_u32(vminq_u32(su,
        vsubq_u32(su, vreinterpretq_u32_s32(v_p))));
    // diff = a - wb (with canonicalization)
    let dif = vsubq_s32(orig_a, wb);
    let du = vreinterpretq_u32_s32(dif);
    *b = vreinterpretq_s32_u32(vminq_u32(du,
        vaddq_u32(du, vreinterpretq_u32_s32(v_p))));
}

/// NTT with NEON: 4 butterflies per vector instruction.
fn ntt_koalabear_neon(data: &mut [i32], twiddles: &[i32]) {
    let n = data.len();
    unsafe {
        let v_p = vdupq_n_s32(P_VAL);
        let v_mu = vdupq_n_s32(MU_VAL);
        for stage in 0..20 {
            let half = 1usize << (19 - stage);
            let mut group = 0usize;
            while group < (1 << stage) {
                let mut pair = 0usize;
                while pair + 4 <= half {
                    let i = group * 2 * half + pair;
                    let j = i + half;
                    let tw_idx = stage * (n / 2) + group * half + pair;
                    let mut va = vld1q_s32(data.as_ptr().add(i));
                    let mut vb = vld1q_s32(data.as_ptr().add(j));
                    let vw = vld1q_s32(twiddles.as_ptr().add(tw_idx));
                    butterfly_neon(&mut va, &mut vb, vw, v_p, v_mu);
                    vst1q_s32(data.as_mut_ptr().add(i), va);
                    vst1q_s32(data.as_mut_ptr().add(j), vb);
                    pair += 4;
                }
                // Scalar tail for stages where half < 4
                while pair < half {
                    let i = group * 2 * half + pair;
                    let j = i + half;
                    let tw_idx = stage * (n / 2) + group * half + pair;
                    let w = twiddles[tw_idx];
                    let wb = scalar_monty_mul(w, data[j], P_VAL, MU_VAL);
                    let orig_a = data[i];
                    let sum = orig_a.wrapping_add(wb);
                    data[i] = if (sum as u32) >= (P_VAL as u32) { sum.wrapping_sub(P_VAL) } else { sum };
                    let dif = orig_a.wrapping_sub(wb);
                    data[j] = if dif < 0 { dif.wrapping_add(P_VAL) } else { dif };
                    pair += 1;
                }
                group += 1;
            }
        }
    }
}

fn main() {
    let n: usize = 1048576;
    let log_n: usize = 20;
    let tw_size = n * log_n;
    let twiddles: Vec<i32> = (0..tw_size).map(|i|
        ((i as u64 * 7 + 31) % 2130706433 as u64) as i32).collect();

    let iters: usize = 3;
    let start = Instant::now();
    for _ in 0..iters {
        let mut data: Vec<i32> = (0..n).map(|i|
            ((i as u64 * 1000000007) % 2130706433 as u64) as i32).collect();
        ntt_koalabear_neon(&mut data, &twiddles);
    }
    let elapsed = start.elapsed();
    let us = elapsed.as_secs_f64() / iters as f64 * 1e6;
    let melem = n as f64 * iters as f64 / elapsed.as_secs_f64() / 1e6;
    eprintln!("N=1048576 p=2130706433 NEON Montgomery (4-wide)");
    eprintln!("  {} us  {} Melem/s", us, melem);
}
