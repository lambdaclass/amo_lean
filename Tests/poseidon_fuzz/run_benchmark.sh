#!/bin/bash
# Phase 4b Extended: Benchmark Comparison Script
# Compares C implementation vs HorizenLabs Rust oracle

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
POSEIDON_C_DIR="$SCRIPT_DIR/../poseidon_c"

echo "================================================================="
echo "  Phase 4b Extended: C vs Rust Benchmark Comparison"
echo "================================================================="
echo ""

# Default iterations
ITERATIONS=${1:-1000000}
echo "Iterations: $ITERATIONS"
echo ""

# Build C runner
echo "Building C implementation..."
cd "$POSEIDON_C_DIR"
gcc -O3 -march=native -o runner_fuzz runner_fuzz.c bn254_field.c -Wall -Wextra 2>/dev/null
echo "  Done"

# Build Rust
echo "Building Rust implementation..."
cd "$SCRIPT_DIR"
cargo build --release --bin bench_rust 2>/dev/null
echo "  Done"
echo ""

# Run C benchmark
echo "================================================================="
echo "  Running C Benchmark..."
echo "================================================================="
cd "$POSEIDON_C_DIR"
C_RESULT=$(./runner_fuzz --bench "$ITERATIONS" 2>&1 | grep "BENCHMARK_RESULT_C")
C_NS=$(echo "$C_RESULT" | awk '{print $3}')
C_TPS=$(echo "$C_RESULT" | awk '{print $4}')
echo "  Per hash:   $C_NS ns"
echo "  Throughput: $C_TPS hashes/sec"
echo ""

# Run Rust benchmark
echo "================================================================="
echo "  Running Rust Benchmark..."
echo "================================================================="
cd "$SCRIPT_DIR"
RUST_RESULT=$(cargo run --release --bin bench_rust -- "$ITERATIONS" 42 2>&1 | grep "BENCHMARK_RESULT_RUST")
RUST_NS=$(echo "$RUST_RESULT" | awk '{print $3}')
RUST_TPS=$(echo "$RUST_RESULT" | awk '{print $4}')
echo "  Per hash:   $RUST_NS ns"
echo "  Throughput: $RUST_TPS hashes/sec"
echo ""

# Calculate ratio
RATIO=$(echo "scale=2; $C_NS / $RUST_NS" | bc)

echo "================================================================="
echo "  COMPARISON SUMMARY"
echo "================================================================="
echo ""
echo "  Implementation          Per Hash (ns)    Throughput (H/s)"
echo "  ---------------------------------------------------------"
printf "  C (our impl)            %10.1f       %10.0f\n" "$C_NS" "$C_TPS"
printf "  Rust (HorizenLabs)      %10.1f       %10.0f\n" "$RUST_NS" "$RUST_TPS"
echo "  ---------------------------------------------------------"
echo "  Ratio (C/Rust):         $RATIO x"
echo ""
echo "================================================================="
