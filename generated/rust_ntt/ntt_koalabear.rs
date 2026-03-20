//! AMO-Lean Generated Rust NTT — e-graph cost model selection
//! N = 1048576, p = 2130706433
//! Reduction: solinasFold, Word: u32
//! Compile: rustc -O -o ntt_bench this_file.rs
//! Same trust boundary as Fiat-Crypto (verified lowering via Trust-Lean)

use std::time::Instant;

const P: u32 = 2130706433;

#[inline(always)]
fn solinas_fold(x: u64) -> u32 {
    (((x >> 31) as u64).wrapping_mul(1 as u64))
        .wrapping_add(x & 2147483647 as u64) as u32
}

#[inline(always)]
fn butterfly(a: &mut u32, b: &mut u32, w: u32) {
    let orig_a = *a;
    let wb = solinas_fold((w as u64).wrapping_mul(*b as u64));
    *a = solinas_fold((orig_a as u64).wrapping_add(wb as u64));
    *b = solinas_fold((2130706433 as u64).wrapping_add(orig_a as u64).wrapping_sub(wb as u64));
}

fn ntt_koalabear(data: &mut [u32], twiddles: &[u32]) {
    let n = data.len();
    for stage in 0..20 {
        let half = 1 << (19 - stage);
        let mut group = 0;
        while group < (1 << stage) {
            let mut pair = 0;
            while pair + 1 <= half {
                let i = group * 2 * half + pair;
                let j = i + half;
                let tw_idx = stage * (n / 2) + group * half + pair;
                let w = twiddles[tw_idx];
                // split_at_mut to satisfy borrow checker (i < j always)
                let (left, right) = data.split_at_mut(j);
                butterfly(&mut left[i], &mut right[0], w);
                pair += 1;
            }
            group += 1;
        }
    }
}

fn main() {
    let n: usize = 1048576;
    let log_n: usize = 20;
    let tw_size = n * log_n;
    let twiddles: Vec<u32> = (0..tw_size).map(|i| ((i as u64 * 7 + 31) % P as u64) as u32).collect();

    let iters: usize = 3;
    let start = Instant::now();
    for _ in 0..iters {
        let mut data: Vec<u32> = (0..n).map(|i| ((i as u64 * 1000000007) % P as u64) as u32).collect();
        ntt_koalabear(&mut data, &twiddles);
    }
    let elapsed = start.elapsed();
    let us = elapsed.as_secs_f64() / iters as f64 * 1e6;
    let melem = n as f64 * iters as f64 / elapsed.as_secs_f64() / 1e6;
    eprintln!("N=1048576 p=2130706433 (solinasFold)");
    eprintln!("  {} us  {} Melem/s", us, melem);
}
