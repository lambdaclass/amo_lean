#!/bin/bash
# Goldilocks NTT Benchmark: TRZK Verified Scalar vs Plonky3
# Usage: ./run_goldi_bench.sh [logN] (default: 20)
set -e
cd "$(dirname "$0")/../.."

LOGN=${1:-20}
N=$((1 << LOGN))
ITERS=10
P3_LIB=verification/plonky3/plonky3_shim/target/release
TMP=$(mktemp -d)

echo "=== Goldilocks NTT Benchmark: N=2^${LOGN} (${N} elements) ==="

# Step 1: Generate TRZK verified NTT (C scalar)
echo "[1/4] Generating TRZK verified NTT..."
lake env lean --run Tests/benchmark/emit_code.lean goldilocks $LOGN c arm-scalar 2>/dev/null > $TMP/trzk_ntt.c

# Step 2: Extract just the NTT function
NTT_FUNC=$(grep "void goldilocks_ntt_ultra" $TMP/trzk_ntt.c | head -1 | sed 's/void //' | sed 's/(.*//')
echo "    Function: ${NTT_FUNC}"

# Step 3: Build benchmark harness
cat > $TMP/bench.c << BENCHEOF
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define GOLDI_P 18446744069414584321ULL

/* Plonky3 FFI */
extern int plonky3_ntt_forward(uint64_t* data, size_t len);

/* Include TRZK NTT */
$(awk '/^int main/{exit} {print}' $TMP/trzk_ntt.c)

static uint64_t mod_pow_u64(uint64_t base, uint64_t exp, uint64_t m) {
    unsigned __int128 result = 1, b = base;
    b %= m;
    while (exp > 0) {
        if (exp & 1) result = (result * b) % m;
        b = (b * b) % m;
        exp >>= 1;
    }
    return (uint64_t)result;
}

static double elapsed_us(struct timespec *t0, struct timespec *t1) {
    return ((t1->tv_sec - t0->tv_sec) * 1e6 + (t1->tv_nsec - t0->tv_nsec) / 1e3);
}

int main(void) {
    const size_t n = ${N};
    const size_t logn = ${LOGN};
    const int iters = ${ITERS};

    uint64_t *data_trzk = (uint64_t*)malloc(n * sizeof(uint64_t));
    uint64_t *data_p3 = (uint64_t*)malloc(n * sizeof(uint64_t));
    uint64_t *tw = (uint64_t*)malloc(n * logn * sizeof(uint64_t));

    /* Init data */
    for (size_t i = 0; i < n; i++)
        data_trzk[i] = (uint64_t)(((unsigned __int128)i * 1000000007) % GOLDI_P);
    memcpy(data_p3, data_trzk, n * sizeof(uint64_t));

    /* Twiddles (plain, for TRZK) */
    uint64_t omega = mod_pow_u64(7, (GOLDI_P - 1) / n, GOLDI_P);
    for (size_t st = 0; st < logn; st++) {
        size_t h = 1u << (logn - 1 - st);
        for (size_t g = 0; g < (1u << st); g++)
            for (size_t p = 0; p < h; p++)
                tw[st*(n/2) + g*h + p] = mod_pow_u64(omega, p*(1ULL<<st), GOLDI_P);
    }

    struct timespec t0, t1;
    double trzk_us = 0, p3_us = 0;

    /* Warmup */
    ${NTT_FUNC}(data_trzk, tw);
    memcpy(data_trzk, data_p3, n * sizeof(uint64_t));
    plonky3_ntt_forward(data_p3, n);
    memcpy(data_p3, data_trzk, n * sizeof(uint64_t));

    /* Benchmark TRZK */
    for (int iter = 0; iter < iters; iter++) {
        memcpy(data_trzk, data_p3, n * sizeof(uint64_t));
        clock_gettime(CLOCK_MONOTONIC, &t0);
        ${NTT_FUNC}(data_trzk, tw);
        clock_gettime(CLOCK_MONOTONIC, &t1);
        trzk_us += elapsed_us(&t0, &t1);
    }
    trzk_us /= iters;

    /* Benchmark Plonky3 */
    for (int iter = 0; iter < iters; iter++) {
        memcpy(data_p3, data_trzk, n * sizeof(uint64_t));
        clock_gettime(CLOCK_MONOTONIC, &t0);
        plonky3_ntt_forward(data_p3, n);
        clock_gettime(CLOCK_MONOTONIC, &t1);
        p3_us += elapsed_us(&t0, &t1);
    }
    p3_us /= iters;

    double ratio = trzk_us / p3_us;
    double melem_trzk = (double)n / trzk_us;
    double melem_p3 = (double)n / p3_us;

    printf("# Goldilocks NTT Benchmark (N=2^%zu = %zu, %d iterations)\n", logn, n, iters);
    printf("TRZK Verified Scalar:  %8.1f µs  (%5.1f Melem/s)\n", trzk_us, melem_trzk);
    printf("Plonky3 Radix-2 DIT:   %8.1f µs  (%5.1f Melem/s)\n", p3_us, melem_p3);
    printf("Ratio TRZK/Plonky3:    %.2fx %s\n", ratio,
           ratio < 1.0 ? "(TRZK faster)" : ratio > 1.0 ? "(Plonky3 faster)" : "(equal)");

    free(data_trzk);
    free(data_p3);
    free(tw);
    return 0;
}
BENCHEOF

# Step 4: Compile and run
echo "[2/4] Compiling..."
cc -O2 -Wno-implicitly-unsigned-literal $TMP/bench.c \
  -L${P3_LIB} -lplonky3_shim -o $TMP/bench

echo "[3/4] Running benchmark..."
DYLD_LIBRARY_PATH=${P3_LIB} $TMP/bench

echo "[4/4] Done."
rm -rf $TMP
