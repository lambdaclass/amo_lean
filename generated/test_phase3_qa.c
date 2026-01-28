/**
 * test_phase3_qa.c - Comprehensive Phase 3 QA Test Suite
 *
 * AMO-Lean Phase 3 Quality Assurance
 *
 * This test suite validates:
 * 1. SIMD primitive correctness (add, sub, mul, FRI fold)
 * 2. Memory alignment handling
 * 3. Tail/boundary processing
 * 4. Performance benchmarks with acceptance criteria
 *
 * Compile:
 *   clang -O3 -mavx2 -o test_phase3_qa test_phase3_qa.c -lm
 *
 * With sanitizers:
 *   clang -O1 -g -mavx2 -fsanitize=address,undefined -o test_phase3_qa test_phase3_qa.c -lm
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <time.h>
#include <math.h>

#define FIELD_GOLDILOCKS
#include "field_goldilocks.h"
#include "field_goldilocks_avx2.h"
#include "fri_fold_avx2.h"

/*===========================================================================
 * Test Infrastructure
 *===========================================================================*/

static int tests_passed = 0;
static int tests_failed = 0;
static int tests_skipped = 0;

#define TEST_SECTION(name) printf("\n╔══════════════════════════════════════════════════════════════╗\n"); \
                           printf("║ %-60s ║\n", name); \
                           printf("╚══════════════════════════════════════════════════════════════╝\n\n")

#define TEST(name) printf("  [TEST] %s... ", name); fflush(stdout)
#define PASS() do { printf("✅ PASS\n"); tests_passed++; } while(0)
#define FAIL(msg) do { printf("❌ FAIL: %s\n", msg); tests_failed++; } while(0)
#define SKIP(msg) do { printf("⏭️  SKIP: %s\n", msg); tests_skipped++; } while(0)

/* PRNG for reproducible tests */
static uint64_t prng_state = 0xDEADBEEFCAFEBABEULL;

static uint64_t rand_field(void) {
    prng_state ^= prng_state << 13;
    prng_state ^= prng_state >> 7;
    prng_state ^= prng_state << 17;
    return prng_state % GOLDILOCKS_P;
}

/*===========================================================================
 * 1. UNIT TESTING DE PRIMITIVAS SIMD
 *===========================================================================*/

/**
 * Test 1.1: Multiplicación con valores aleatorios
 */
static bool test_mul_random(void) {
    const int NUM_TESTS = 1000;

    for (int t = 0; t < NUM_TESTS; t++) {
        uint64_t a[4] __attribute__((aligned(32)));
        uint64_t b[4] __attribute__((aligned(32)));
        uint64_t result[4] __attribute__((aligned(32)));

        for (int i = 0; i < 4; i++) {
            a[i] = rand_field();
            b[i] = rand_field();
        }

        __m256i va = goldilocks_avx2_load(a);
        __m256i vb = goldilocks_avx2_load(b);
        __m256i vr = goldilocks_avx2_mul(va, vb);
        goldilocks_avx2_store(result, vr);

        for (int i = 0; i < 4; i++) {
            uint64_t expected = goldilocks_mul(a[i], b[i]);
            if (result[i] != expected) {
                printf("\n    Iteration %d, lane %d: a=%lu, b=%lu, got=%lu, expected=%lu\n",
                       t, i, a[i], b[i], result[i], expected);
                return false;
            }
        }
    }
    return true;
}

/**
 * Test 1.2: Caso Borde Crítico - Valores mixtos [P-1, P-1, 0, 1]
 *
 * Verifica que la lógica de reducción SIMD no corrompe carriles vecinos
 * cuando hay valores extremos adyacentes.
 */
static bool test_mul_mixed_extremes(void) {
    /* Caso 1: [P-1, P-1, 0, 1] × [P-1, P-1, 0, 1] */
    uint64_t a1[4] __attribute__((aligned(32))) = {
        GOLDILOCKS_P - 1,  /* Máximo valor */
        GOLDILOCKS_P - 1,  /* Máximo valor */
        0,                  /* Cero */
        1                   /* Uno */
    };
    uint64_t b1[4] __attribute__((aligned(32))) = {
        GOLDILOCKS_P - 1,
        GOLDILOCKS_P - 1,
        0,
        1
    };
    uint64_t result1[4] __attribute__((aligned(32)));

    __m256i va1 = goldilocks_avx2_load(a1);
    __m256i vb1 = goldilocks_avx2_load(b1);
    __m256i vr1 = goldilocks_avx2_mul(va1, vb1);
    goldilocks_avx2_store(result1, vr1);

    for (int i = 0; i < 4; i++) {
        uint64_t expected = goldilocks_mul(a1[i], b1[i]);
        if (result1[i] != expected) {
            printf("\n    Case 1, lane %d: expected=%lu, got=%lu\n", i, expected, result1[i]);
            return false;
        }
    }

    /* Caso 2: Patrón alternante [P-1, 0, P-1, 0] × [1, P-1, 1, P-1] */
    uint64_t a2[4] __attribute__((aligned(32))) = {
        GOLDILOCKS_P - 1, 0, GOLDILOCKS_P - 1, 0
    };
    uint64_t b2[4] __attribute__((aligned(32))) = {
        1, GOLDILOCKS_P - 1, 1, GOLDILOCKS_P - 1
    };
    uint64_t result2[4] __attribute__((aligned(32)));

    __m256i va2 = goldilocks_avx2_load(a2);
    __m256i vb2 = goldilocks_avx2_load(b2);
    __m256i vr2 = goldilocks_avx2_mul(va2, vb2);
    goldilocks_avx2_store(result2, vr2);

    for (int i = 0; i < 4; i++) {
        uint64_t expected = goldilocks_mul(a2[i], b2[i]);
        if (result2[i] != expected) {
            printf("\n    Case 2, lane %d: expected=%lu, got=%lu\n", i, expected, result2[i]);
            return false;
        }
    }

    /* Caso 3: Valores cerca del borde de reducción [EPSILON, EPSILON+1, 2^32, 2^32-1] */
    uint64_t a3[4] __attribute__((aligned(32))) = {
        GOLDILOCKS_EPSILON,
        GOLDILOCKS_EPSILON + 1,
        1ULL << 32,
        (1ULL << 32) - 1
    };
    uint64_t b3[4] __attribute__((aligned(32))) = {
        GOLDILOCKS_EPSILON,
        GOLDILOCKS_EPSILON,
        GOLDILOCKS_EPSILON,
        GOLDILOCKS_EPSILON
    };
    uint64_t result3[4] __attribute__((aligned(32)));

    __m256i va3 = goldilocks_avx2_load(a3);
    __m256i vb3 = goldilocks_avx2_load(b3);
    __m256i vr3 = goldilocks_avx2_mul(va3, vb3);
    goldilocks_avx2_store(result3, vr3);

    for (int i = 0; i < 4; i++) {
        uint64_t expected = goldilocks_mul(a3[i], b3[i]);
        if (result3[i] != expected) {
            printf("\n    Case 3, lane %d: a=%lu, b=%lu, expected=%lu, got=%lu\n",
                   i, a3[i], b3[i], expected, result3[i]);
            return false;
        }
    }

    return true;
}

/*===========================================================================
 * 2. TEST DE ALINEACIÓN Y FRONTERAS (MEMORY SAFETY)
 *===========================================================================*/

/**
 * Test 2.1: Acceso a memoria desalineada
 *
 * Verifica que las funciones loadu/storeu manejan punteros no alineados.
 */
static bool test_unaligned_access(void) {
    /* Allocate extra space for misalignment */
    uint8_t buffer[64 + 32] __attribute__((aligned(64)));

    /* Test different offsets */
    for (int offset = 0; offset < 32; offset += 8) {
        uint64_t *a = (uint64_t *)(buffer + offset);
        uint64_t *b = (uint64_t *)(buffer + offset + 32);

        /* Initialize with known values */
        for (int i = 0; i < 4; i++) {
            a[i] = (uint64_t)(i + 1) * 1000000007ULL % GOLDILOCKS_P;
            b[i] = (uint64_t)(i + 5) * 1000000009ULL % GOLDILOCKS_P;
        }

        /* Use unaligned load/store */
        __m256i va = goldilocks_avx2_loadu(a);
        __m256i vb = goldilocks_avx2_loadu(b);
        __m256i vr = goldilocks_avx2_add(va, vb);

        uint64_t result[4] __attribute__((aligned(32)));
        goldilocks_avx2_store(result, vr);

        /* Verify */
        for (int i = 0; i < 4; i++) {
            uint64_t expected = goldilocks_add(a[i], b[i]);
            if (result[i] != expected) {
                printf("\n    Offset %d, lane %d: expected=%lu, got=%lu\n",
                       offset, i, expected, result[i]);
                return false;
            }
        }
    }

    return true;
}

/**
 * Test 2.2: Tail Processing - Tamaños no divisibles por 4
 *
 * Ejecuta FRI fold sobre inputs de tamaños incómodos (primos, no potencias de 2).
 */
/* Round up to multiple of 32 for aligned_alloc */
static inline size_t round_up_32(size_t n) {
    return (n + 31) & ~(size_t)31;
}

static bool test_tail_processing(void) {
    /* Test sizes: primos y tamaños incómodos */
    const size_t test_sizes[] = {1, 2, 3, 5, 7, 11, 13, 17, 23, 31, 61, 127, 1023};
    const int num_sizes = sizeof(test_sizes) / sizeof(test_sizes[0]);

    for (int s = 0; s < num_sizes; s++) {
        size_t n = test_sizes[s];

        /* Allocate with padding for safety, rounded up to multiple of 32 */
        size_t alloc_size = round_up_32((n + 4) * sizeof(uint64_t));
        uint64_t *even = aligned_alloc(32, alloc_size);
        uint64_t *odd = aligned_alloc(32, alloc_size);
        uint64_t *result_avx2 = aligned_alloc(32, alloc_size);
        uint64_t *result_scalar = aligned_alloc(32, alloc_size);

        if (!even || !odd || !result_avx2 || !result_scalar) {
            printf("\n    Failed to allocate memory for size %zu\n", n);
            free(even); free(odd); free(result_avx2); free(result_scalar);
            return false;
        }

        /* Initialize with random values */
        for (size_t i = 0; i < n; i++) {
            even[i] = rand_field();
            odd[i] = rand_field();
        }
        /* Poison padding to detect overflows */
        for (size_t i = n; i < n + 4; i++) {
            even[i] = 0xDEADDEADDEADDEADULL;
            odd[i] = 0xDEADDEADDEADDEADULL;
            result_avx2[i] = 0xDEADDEADDEADDEADULL;
            result_scalar[i] = 0xDEADDEADDEADDEADULL;
        }

        uint64_t alpha = rand_field();

        /* AVX2 FRI fold */
        fri_fold_avx2(n, even, odd, result_avx2, alpha);

        /* Scalar reference */
        for (size_t i = 0; i < n; i++) {
            result_scalar[i] = goldilocks_add(even[i], goldilocks_mul(alpha, odd[i]));
        }

        /* Compare results */
        bool match = true;
        for (size_t i = 0; i < n; i++) {
            if (result_avx2[i] != result_scalar[i]) {
                printf("\n    Size %zu, index %zu: AVX2=%lu, scalar=%lu\n",
                       n, i, result_avx2[i], result_scalar[i]);
                match = false;
                break;
            }
        }

        /* Check that padding wasn't corrupted */
        for (size_t i = n; i < n + 4; i++) {
            if (result_avx2[i] != 0xDEADDEADDEADDEADULL) {
                printf("\n    Size %zu: Buffer overflow detected at padding index %zu\n", n, i);
                match = false;
                break;
            }
        }

        free(even);
        free(odd);
        free(result_avx2);
        free(result_scalar);

        if (!match) return false;
    }

    return true;
}

/*===========================================================================
 * 3. BENCHMARK DE THROUGHPUT
 *===========================================================================*/

#define BENCH_WARMUP 100000
#define BENCH_ITERATIONS 10000000

typedef struct {
    double scalar_throughput;   /* M ops/s */
    double avx2_throughput;     /* M ops/s */
    double speedup;
    bool meets_criteria;        /* >= 1.5x */
} BenchmarkResult;

/**
 * Test 3.1: Benchmark de multiplicación
 */
static BenchmarkResult benchmark_multiplication(void) {
    BenchmarkResult result = {0};

    uint64_t a[4] __attribute__((aligned(32)));
    uint64_t b[4] __attribute__((aligned(32)));

    for (int i = 0; i < 4; i++) {
        a[i] = rand_field();
        b[i] = rand_field();
    }

    /* Scalar benchmark */
    uint64_t sa = a[0], sb = b[0], sr;

    /* Warmup */
    for (int i = 0; i < BENCH_WARMUP; i++) {
        sr = goldilocks_mul(sa, sb);
        sa ^= sr;
    }
    sa = a[0];

    clock_t start = clock();
    for (int i = 0; i < BENCH_ITERATIONS; i++) {
        sr = goldilocks_mul(sa, sb);
        sa ^= sr;
    }
    clock_t end = clock();

    double scalar_time = (double)(end - start) / CLOCKS_PER_SEC;
    result.scalar_throughput = (double)BENCH_ITERATIONS / scalar_time / 1e6;

    /* AVX2 benchmark */
    __m256i va = goldilocks_avx2_load(a);
    __m256i vb = goldilocks_avx2_load(b);
    __m256i vr;

    /* Warmup */
    for (int i = 0; i < BENCH_WARMUP; i++) {
        vr = goldilocks_avx2_mul(va, vb);
        va = _mm256_xor_si256(va, vr);
    }
    va = goldilocks_avx2_load(a);

    start = clock();
    for (int i = 0; i < BENCH_ITERATIONS; i++) {
        vr = goldilocks_avx2_mul(va, vb);
        va = _mm256_xor_si256(va, vr);
    }
    end = clock();

    double avx2_time = (double)(end - start) / CLOCKS_PER_SEC;
    result.avx2_throughput = (4.0 * BENCH_ITERATIONS) / avx2_time / 1e6;

    result.speedup = result.avx2_throughput / result.scalar_throughput;
    result.meets_criteria = result.speedup >= 1.5;

    return result;
}

/**
 * Test 3.2: Benchmark de FRI Fold
 */
static BenchmarkResult benchmark_fri_fold(void) {
    BenchmarkResult result = {0};

    const size_t N = 1024;
    const int ITERS = 100000;  /* More iterations for measurable time */
    uint64_t *even = aligned_alloc(32, N * sizeof(uint64_t));
    uint64_t *odd = aligned_alloc(32, N * sizeof(uint64_t));
    uint64_t *out = aligned_alloc(32, N * sizeof(uint64_t));

    for (size_t i = 0; i < N; i++) {
        even[i] = rand_field();
        odd[i] = rand_field();
    }
    uint64_t alpha = rand_field();

    /* Scalar benchmark */
    for (int w = 0; w < 1000; w++) {
        for (size_t i = 0; i < N; i++) {
            out[i] = goldilocks_add(even[i], goldilocks_mul(alpha, odd[i]));
        }
    }

    clock_t start = clock();
    for (int iter = 0; iter < ITERS; iter++) {
        for (size_t i = 0; i < N; i++) {
            out[i] = goldilocks_add(even[i], goldilocks_mul(alpha, odd[i]));
        }
    }
    clock_t end = clock();

    double scalar_time = (double)(end - start) / CLOCKS_PER_SEC;
    /* Guard against division by zero */
    if (scalar_time < 0.001) scalar_time = 0.001;
    result.scalar_throughput = ((double)ITERS * N) / scalar_time / 1e6;

    /* AVX2 benchmark */
    for (int w = 0; w < 1000; w++) {
        fri_fold_avx2(N, even, odd, out, alpha);
    }

    start = clock();
    for (int iter = 0; iter < ITERS; iter++) {
        fri_fold_avx2(N, even, odd, out, alpha);
    }
    end = clock();

    double avx2_time = (double)(end - start) / CLOCKS_PER_SEC;
    /* Guard against division by zero */
    if (avx2_time < 0.001) avx2_time = 0.001;
    result.avx2_throughput = ((double)ITERS * N) / avx2_time / 1e6;

    result.speedup = result.avx2_throughput / result.scalar_throughput;
    result.meets_criteria = result.speedup >= 1.5;

    free(even);
    free(odd);
    free(out);

    return result;
}

/*===========================================================================
 * 4. REPORTE DE ANÁLISIS
 *===========================================================================*/

static void print_benchmark_report(const char *name, BenchmarkResult r) {
    printf("\n  ┌─────────────────────────────────────────────────────────────┐\n");
    printf("  │ %-61s │\n", name);
    printf("  ├─────────────────────────────────────────────────────────────┤\n");
    printf("  │ Scalar throughput:  %10.2f M ops/s                     │\n", r.scalar_throughput);
    printf("  │ AVX2 throughput:    %10.2f M ops/s                     │\n", r.avx2_throughput);
    printf("  │ Speedup:            %10.2fx                            │\n", r.speedup);
    printf("  │ Criteria (>=1.5x):  %s                                    │\n",
           r.meets_criteria ? "✅ PASS" : "❌ FAIL");
    printf("  └─────────────────────────────────────────────────────────────┘\n");
}

static void print_risk_analysis(BenchmarkResult mul_result, BenchmarkResult fri_result) {
    printf("\n");
    TEST_SECTION("ANÁLISIS DE RIESGOS: MULTIPLICACIÓN 64-BIT EN AVX2");

    printf("  El problema fundamental:\n");
    printf("  AVX2 NO tiene instrucción nativa para multiplicación 64×64→128 bits.\n");
    printf("  Debemos emular usando 4 multiplicaciones de 32 bits (_mm256_mul_epu32).\n\n");

    printf("  Nuestra implementación (basada en Plonky3):\n");
    printf("  - mul64_64: 4× _mm256_mul_epu32 + shifts + adds\n");
    printf("  - reduce128: Reducción usando 2^64 ≡ 2^32-1 (mod p)\n");
    printf("  - Truco vmovehdup_ps: Extrae bits altos sin usar puertos vectoriales\n\n");

    double mul_efficiency = mul_result.speedup / 4.0 * 100;
    double fri_efficiency = fri_result.speedup / 4.0 * 100;

    printf("  Eficiencia de paralelización:\n");
    printf("  - Multiplicación: %.1f%% del ideal teórico (4x)\n", mul_efficiency);
    printf("  - FRI Fold:       %.1f%% del ideal teórico (4x)\n", fri_efficiency);
    printf("\n");

    if (mul_result.speedup < 1.0) {
        printf("  ⚠️  ADVERTENCIA CRÍTICA: La multiplicación AVX2 es MÁS LENTA que escalar.\n");
        printf("      La sobrecarga de emulación 64-bit supera los beneficios de SIMD.\n");
        printf("      Considerar: usar solo para operaciones que puedan usar 32-bit.\n");
    } else if (mul_result.speedup < 1.5) {
        printf("  ⚠️  ADVERTENCIA: Speedup < 1.5x. La implementación no cumple criterio.\n");
        printf("      Posibles causas:\n");
        printf("      - Overhead de emulación 64×64→128\n");
        printf("      - Presión en puertos de ejecución\n");
        printf("      - Dependencias de datos en reducción\n");
    } else if (mul_result.speedup < 2.5) {
        printf("  ℹ️  Speedup aceptable pero subóptimo.\n");
        printf("      Optimizaciones potenciales:\n");
        printf("      - Delayed reduction (acumular antes de reducir)\n");
        printf("      - Mejor scheduling de instrucciones\n");
    } else {
        printf("  ✅ Speedup excelente para multiplicación emulada en AVX2.\n");
    }
}

/*===========================================================================
 * MAIN
 *===========================================================================*/

int main(void) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════════════╗\n");
    printf("║        AMO-LEAN PHASE 3: COMPREHENSIVE QA TEST SUITE             ║\n");
    printf("║                     Quality Assurance Report                     ║\n");
    printf("╚══════════════════════════════════════════════════════════════════╝\n");

    /* ===== SECTION 1: Unit Tests ===== */
    TEST_SECTION("1. UNIT TESTING DE PRIMITIVAS SIMD");

    TEST("Multiplicación con valores aleatorios (1000 iteraciones)");
    if (test_mul_random()) { PASS(); } else { FAIL("Discrepancia AVX2 vs escalar"); }

    TEST("Caso borde crítico: valores mixtos [P-1, P-1, 0, 1]");
    if (test_mul_mixed_extremes()) { PASS(); } else { FAIL("Corrupción entre carriles"); }

    /* ===== SECTION 2: Memory Safety ===== */
    TEST_SECTION("2. TEST DE ALINEACIÓN Y FRONTERAS");

    TEST("Acceso a memoria desalineada (offsets 0-24 bytes)");
    if (test_unaligned_access()) { PASS(); } else { FAIL("Error en acceso desalineado"); }

    TEST("Tail processing: tamaños incómodos (1,2,3,5,7,11,13,17,23,31,61,127,1023)");
    if (test_tail_processing()) { PASS(); } else { FAIL("Error en procesamiento de cola"); }

    /* ===== SECTION 3: Benchmarks ===== */
    TEST_SECTION("3. BENCHMARK DE THROUGHPUT");

    printf("  Ejecutando benchmarks (esto puede tomar varios segundos)...\n\n");

    BenchmarkResult mul_result = benchmark_multiplication();
    print_benchmark_report("Multiplicación Goldilocks", mul_result);

    TEST("Criterio: Multiplicación speedup >= 1.5x");
    if (mul_result.meets_criteria) { PASS(); } else { FAIL("Speedup insuficiente"); }

    BenchmarkResult fri_result = benchmark_fri_fold();
    print_benchmark_report("FRI Fold (N=1024)", fri_result);

    /* Note: FRI fold benchmark is informational only.
     * The scalar loop has no data dependencies, so the compiler can auto-vectorize
     * it with -O3, making AVX2 vs scalar comparison meaningless.
     * The multiplication benchmark correctly measures AVX2 advantage because its
     * scalar version has a dependency chain that prevents auto-vectorization.
     */
    printf("  [INFO] FRI Fold benchmark es solo informativo (el compilador auto-vectoriza escalar)\n");

    /* ===== SECTION 4: Risk Analysis ===== */
    print_risk_analysis(mul_result, fri_result);

    /* ===== SUMMARY ===== */
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════════════╗\n");
    printf("║                         TEST SUMMARY                             ║\n");
    printf("╠══════════════════════════════════════════════════════════════════╣\n");
    printf("║  Tests Passed:  %-4d                                             ║\n", tests_passed);
    printf("║  Tests Failed:  %-4d                                             ║\n", tests_failed);
    printf("║  Tests Skipped: %-4d                                             ║\n", tests_skipped);
    printf("╠══════════════════════════════════════════════════════════════════╣\n");

    if (tests_failed == 0) {
        printf("║  ✅ ALL TESTS PASSED - Phase 3 QA APPROVED                       ║\n");
    } else {
        printf("║  ❌ SOME TESTS FAILED - Phase 3 QA REQUIRES ATTENTION            ║\n");
    }

    printf("╚══════════════════════════════════════════════════════════════════╝\n\n");

    return tests_failed > 0 ? 1 : 0;
}
