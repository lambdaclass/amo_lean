//! Poseidon2 Rust Benchmark
//!
//! Measures throughput of HorizenLabs poseidon2-rs implementation
//! for comparison with our C implementation.

use ark_ff::UniformRand;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use std::env;
use std::time::Instant;
use zkhash::fields::bn256::FpBN256;
use zkhash::poseidon2::poseidon2::Poseidon2;
use zkhash::poseidon2::poseidon2_instance_bn256::POSEIDON2_BN256_PARAMS;

/// Generate a random field element
fn random_field_element(rng: &mut ChaCha20Rng) -> FpBN256 {
    FpBN256::rand(rng)
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let iterations: usize = if args.len() > 1 {
        args[1].parse().unwrap_or(1_000_000)
    } else {
        1_000_000
    };

    let seed: u64 = if args.len() > 2 {
        args[2].parse().unwrap_or(42)
    } else {
        42
    };

    println!("=================================================================");
    println!("  Poseidon2 Rust Benchmark (HorizenLabs implementation)");
    println!("=================================================================");
    println!();
    println!("Configuration:");
    println!("  Iterations: {}", iterations);
    println!("  Seed: {}", seed);
    println!();

    // Initialize Poseidon2
    let poseidon = Poseidon2::new(&POSEIDON2_BN256_PARAMS);

    // Generate random inputs
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let mut inputs: Vec<[FpBN256; 3]> = Vec::with_capacity(iterations);
    for _ in 0..iterations {
        inputs.push([
            random_field_element(&mut rng),
            random_field_element(&mut rng),
            random_field_element(&mut rng),
        ]);
    }

    println!("Running {} permutations...", iterations);

    // Warmup
    for i in 0..1000.min(iterations) {
        let input_vec: Vec<FpBN256> = inputs[i].to_vec();
        let _ = poseidon.permutation(&input_vec);
    }

    // Benchmark
    let start = Instant::now();
    for input in &inputs {
        let input_vec: Vec<FpBN256> = input.to_vec();
        let _ = poseidon.permutation(&input_vec);
    }
    let elapsed = start.elapsed();

    let total_ns = elapsed.as_nanos() as f64;
    let per_hash_ns = total_ns / iterations as f64;
    let hashes_per_sec = 1_000_000_000.0 / per_hash_ns;

    println!();
    println!("=================================================================");
    println!("  RESULTS");
    println!("=================================================================");
    println!("  Total time:       {:.3} seconds", elapsed.as_secs_f64());
    println!("  Per hash:         {:.1} ns", per_hash_ns);
    println!("  Throughput:       {:.0} hashes/second", hashes_per_sec);
    println!("  Throughput:       {:.2} kH/s", hashes_per_sec / 1000.0);
    println!("=================================================================");

    // Output in machine-readable format for comparison script
    println!();
    println!("BENCHMARK_RESULT_RUST: {} {:.1} {:.0}", iterations, per_hash_ns, hashes_per_sec);
}
