//! Poseidon2 Fuzzing Vector Generator
//!
//! Uses HorizenLabs poseidon2-rs as the "Golden Oracle" to generate
//! test vectors for validating our C implementation.
//!
//! Output: JSON file with edge cases and random vectors.

use ark_ff::{BigInteger, PrimeField, UniformRand};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use serde::{Deserialize, Serialize};
use std::env;
use std::fs::File;
use std::io::Write;
use zkhash::fields::bn256::FpBN256;
use zkhash::poseidon2::poseidon2::Poseidon2;
use zkhash::poseidon2::poseidon2_instance_bn256::POSEIDON2_BN256_PARAMS;

/// BN254 scalar field modulus
const BN254_MODULUS: &str =
    "21888242871839275222246405745257275088548364400416034343698204186575808495617";

/// Test vector structure
#[derive(Serialize, Deserialize, Debug)]
struct TestVector {
    input: [String; 3],
    output: [String; 3],
}

/// Complete test vectors file
#[derive(Serialize, Deserialize, Debug)]
struct TestVectors {
    metadata: Metadata,
    edge_cases: Vec<TestVector>,
    random_cases: Vec<TestVector>,
}

#[derive(Serialize, Deserialize, Debug)]
struct Metadata {
    generator: String,
    field: String,
    modulus: String,
    state_size: usize,
    full_rounds: usize,
    partial_rounds: usize,
    seed: u64,
    edge_count: usize,
    random_count: usize,
}

/// Convert FpBN256 to hex string (big-endian, 64 hex chars)
fn fp_to_hex(f: &FpBN256) -> String {
    // FpBN256 implements PrimeField, so we can use into_bigint() directly
    let bytes = f.into_bigint().to_bytes_be();
    format!("0x{}", hex::encode(bytes))
}

/// Run Poseidon2 permutation on input state
fn poseidon2_permute(input: [FpBN256; 3]) -> [FpBN256; 3] {
    let poseidon = Poseidon2::new(&POSEIDON2_BN256_PARAMS);
    let input_vec: Vec<FpBN256> = input.to_vec();
    let output_vec = poseidon.permutation(&input_vec);
    [output_vec[0], output_vec[1], output_vec[2]]
}

/// Generate a random field element
fn random_field_element(rng: &mut ChaCha20Rng) -> FpBN256 {
    // FpBN256 implements UniformRand from ark_ff
    FpBN256::rand(rng)
}

/// Generate edge case vectors
fn generate_edge_cases() -> Vec<TestVector> {
    let mut vectors = Vec::new();

    // Helper to create vector from field elements
    let create_vector = |a: FpBN256, b: FpBN256, c: FpBN256| -> TestVector {
        let input = [a, b, c];
        let output = poseidon2_permute(input);
        TestVector {
            input: [fp_to_hex(&a), fp_to_hex(&b), fp_to_hex(&c)],
            output: [fp_to_hex(&output[0]), fp_to_hex(&output[1]), fp_to_hex(&output[2])],
        }
    };

    // Create field elements directly using FpBN256
    let zero = FpBN256::from(0u64);
    let one = FpBN256::from(1u64);
    let two = FpBN256::from(2u64);
    let _three = FpBN256::from(3u64);

    // Max field element (P-1) = -1 in the field
    let max_fp = -one;
    let almost_max = max_fp - one;

    // Limb boundary values (64-bit boundaries)
    let limb_max = FpBN256::from(u64::MAX);
    // For 2^64, we need to compute it as (2^32)^2
    let two_32 = FpBN256::from(1u64 << 32);
    let limb_boundary = two_32 * two_32;
    // For 2^127, compute as 2^64 * 2^63
    let two_63 = FpBN256::from(1u64 << 63);
    let limb_boundary_2 = limb_boundary * two_63;

    // Edge case 1: All zeros
    vectors.push(create_vector(zero, zero, zero));

    // Edge case 2: All ones
    vectors.push(create_vector(one, one, one));

    // Edge case 3: Sequential [0, 1, 2] - the canonical test vector
    vectors.push(create_vector(zero, one, two));

    // Edge case 4: All max (P-1)
    vectors.push(create_vector(max_fp, max_fp, max_fp));

    // Edge case 5: Mixed zero and max
    vectors.push(create_vector(zero, max_fp, zero));
    vectors.push(create_vector(max_fp, zero, max_fp));

    // Edge case 6: Near-max values
    vectors.push(create_vector(almost_max, almost_max, almost_max));

    // Edge case 7: Limb boundary - max 64-bit value
    vectors.push(create_vector(limb_max, limb_max, limb_max));

    // Edge case 8: Just above 64-bit boundary
    vectors.push(create_vector(limb_boundary, limb_boundary, limb_boundary));

    // Edge case 9: Near 128-bit boundary
    vectors.push(create_vector(limb_boundary_2, limb_boundary_2, limb_boundary_2));

    // Edge case 10: Mix of small and large
    vectors.push(create_vector(one, limb_max, max_fp));
    vectors.push(create_vector(max_fp, one, zero));

    // Edge case 11: Powers of 2
    for i in [1, 2, 4, 8, 16, 32, 63, 64, 127, 128, 192, 253] {
        let pow2: FpBN256 = if i < 64 {
            FpBN256::from(1u64 << i)
        } else {
            // For larger powers, use repeated doubling
            let mut val = one;
            for _ in 0..i {
                val = val + val;
            }
            val
        };
        vectors.push(create_vector(pow2, pow2, pow2));
    }

    // Edge case 12: Specific bit patterns
    let pattern_a = FpBN256::from(0xAAAAAAAAAAAAAAAAu64);
    let pattern_5 = FpBN256::from(0x5555555555555555u64);
    let pattern_f = FpBN256::from(0xFFFFFFFFFFFFFFFFu64);
    vectors.push(create_vector(pattern_a, pattern_5, pattern_f));

    // Edge case 13: Small sequential values
    for i in 0..10u64 {
        let val = FpBN256::from(i);
        vectors.push(create_vector(val, val, val));
    }

    vectors
}

/// Generate random test vectors
fn generate_random_cases(count: usize, seed: u64) -> Vec<TestVector> {
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let mut vectors = Vec::new();

    for _ in 0..count {
        let a = random_field_element(&mut rng);
        let b = random_field_element(&mut rng);
        let c = random_field_element(&mut rng);

        let input = [a, b, c];
        let output = poseidon2_permute(input);

        vectors.push(TestVector {
            input: [fp_to_hex(&a), fp_to_hex(&b), fp_to_hex(&c)],
            output: [fp_to_hex(&output[0]), fp_to_hex(&output[1]), fp_to_hex(&output[2])],
        });
    }

    vectors
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let random_count: usize = if args.len() > 1 {
        args[1].parse().unwrap_or(10000)
    } else {
        10000
    };

    let seed: u64 = if args.len() > 2 {
        args[2].parse().unwrap_or(42)
    } else {
        42
    };

    let output_file = if args.len() > 3 {
        args[3].clone()
    } else {
        "vectors.json".to_string()
    };

    println!("=================================================================");
    println!("  Poseidon2 Fuzzing Vector Generator (HorizenLabs Oracle)");
    println!("=================================================================");
    println!();
    println!("Configuration:");
    println!("  Random vectors: {}", random_count);
    println!("  Seed: {}", seed);
    println!("  Output: {}", output_file);
    println!();

    // Generate edge cases
    print!("Generating edge cases... ");
    let edge_cases = generate_edge_cases();
    println!("{} vectors", edge_cases.len());

    // Generate random cases
    print!("Generating random cases... ");
    let random_cases = generate_random_cases(random_count, seed);
    println!("{} vectors", random_cases.len());

    // Create output structure
    let vectors = TestVectors {
        metadata: Metadata {
            generator: "HorizenLabs poseidon2-rs".to_string(),
            field: "BN254 scalar field".to_string(),
            modulus: BN254_MODULUS.to_string(),
            state_size: 3,
            full_rounds: 8,
            partial_rounds: 56,
            seed,
            edge_count: edge_cases.len(),
            random_count: random_cases.len(),
        },
        edge_cases,
        random_cases,
    };

    // Write to file
    print!("Writing to {}... ", output_file);
    let json = serde_json::to_string_pretty(&vectors).expect("Failed to serialize");
    let mut file = File::create(&output_file).expect("Failed to create file");
    file.write_all(json.as_bytes()).expect("Failed to write");
    println!("done");

    let total = vectors.metadata.edge_count + vectors.metadata.random_count;
    println!();
    println!("=================================================================");
    println!("  Generated {} total vectors", total);
    println!("  - {} edge cases", vectors.metadata.edge_count);
    println!("  - {} random cases", vectors.metadata.random_count);
    println!("=================================================================");
}
