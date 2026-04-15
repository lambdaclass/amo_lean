/*
 * Goldilocks NTT Benchmark: TRZK Verified vs Plonky3
 * Compares our verified scalar NTT against Plonky3's Radix-2 DIT.
 * Links against libplonky3_shim.dylib for the Plonky3 reference.
 *
 * Compile:
 *   cc -O2 -o bench_goldi_vs_p3 bench_goldi_vs_plonky3.c \
 *     -L../../verification/plonky3/plonky3_shim/target/release \
 *     -lplonky3_shim -Wno-implicitly-unsigned-literal
 *
 * Run:
 *   DYLD_LIBRARY_PATH=../../verification/plonky3/plonky3_shim/target/release \
 *     ./bench_goldi_vs_p3
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define GOLDI_P 18446744069414584321ULL

/* Plonky3 FFI */
extern int plonky3_ntt_forward(uint64_t* data, size_t len);

/* TRZK verified NTT — will be pasted below by the benchmark script */
