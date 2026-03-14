/**
 * test_comprehensive.c - Comprehensive Interoperability Test Suite
 *
 * B94: Validates AMO-Lean generated C code against hardcoded test vectors.
 *
 * Tests:
 *   1. Goldilocks field arithmetic (add, sub, mul, inv, pow, sbox)
 *   2. NTT roundtrip (forward + inverse = identity) for N=8
 *   3. Poseidon2 (skipped — BN254 headers require external constants)
 *
 * Test vectors are hardcoded from known Goldilocks field properties:
 *   P = 2^64 - 2^32 + 1 = 0xFFFFFFFF00000001
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

/* Include Goldilocks field implementation */
#include "../../generated/field_goldilocks.h"

/* NTT skeleton (provides ntt_forward, ntt_inverse) */
#include "../../generated/ntt_kernel.h"
#include "../../generated/ntt_skeleton.c"

/*===========================================================================
 * Test Infrastructure
 *===========================================================================*/

static int tests_run    = 0;
static int tests_passed = 0;
static int tests_failed = 0;

#define P GOLDILOCKS_ORDER  /* 0xFFFFFFFF00000001 */

#define TEST(name, cond) do {                                       \
    tests_run++;                                                    \
    if (cond) {                                                     \
        tests_passed++;                                             \
        printf("  PASS: %s\n", name);                               \
    } else {                                                        \
        tests_failed++;                                             \
        printf("  FAIL: %s\n", name);                               \
    }                                                               \
} while (0)

#define TEST_EQ(name, got, expected) do {                           \
    tests_run++;                                                    \
    uint64_t _g = (got), _e = (expected);                           \
    if (_g == _e) {                                                 \
        tests_passed++;                                             \
        printf("  PASS: %s\n", name);                               \
    } else {                                                        \
        tests_failed++;                                             \
        printf("  FAIL: %s (got 0x%016llx, expected 0x%016llx)\n",  \
               name, (unsigned long long)_g,                        \
               (unsigned long long)_e);                             \
    }                                                               \
} while (0)

/*===========================================================================
 * 1. Field Arithmetic Tests
 *===========================================================================*/

static void test_field_add(void) {
    printf("\n[Field Addition]\n");

    /* Basic: 1 + 2 = 3 */
    TEST_EQ("add(1, 2) = 3", goldilocks_add(1, 2), 3);

    /* Identity: a + 0 = a */
    TEST_EQ("add(42, 0) = 42", goldilocks_add(42, 0), 42);

    /* Commutativity: a + b = b + a */
    TEST_EQ("add(3, 7) = add(7, 3)",
            goldilocks_add(3, 7), goldilocks_add(7, 3));

    /* Wrap-around: (P-1) + 1 = 0 mod P */
    TEST_EQ("add(P-1, 1) = 0", goldilocks_add(P - 1, 1), 0);

    /* Wrap-around: (P-1) + 2 = 1 mod P */
    TEST_EQ("add(P-1, 2) = 1", goldilocks_add(P - 1, 2), 1);

    /* (P-1) + (P-1) = P-2 mod P  (since 2P-2 mod P = P-2) */
    TEST_EQ("add(P-1, P-1) = P-2", goldilocks_add(P - 1, P - 1), P - 2);
}

static void test_field_sub(void) {
    printf("\n[Field Subtraction]\n");

    /* Basic: 5 - 3 = 2 */
    TEST_EQ("sub(5, 3) = 2", goldilocks_sub(5, 3), 2);

    /* Identity: a - 0 = a */
    TEST_EQ("sub(42, 0) = 42", goldilocks_sub(42, 0), 42);

    /* Self: a - a = 0 */
    TEST_EQ("sub(7, 7) = 0", goldilocks_sub(7, 7), 0);

    /* Underflow: 0 - 1 = P-1 mod P */
    TEST_EQ("sub(0, 1) = P-1", goldilocks_sub(0, 1), P - 1);

    /* Underflow: 3 - 5 = P-2 */
    TEST_EQ("sub(3, 5) = P-2", goldilocks_sub(3, 5), P - 2);

    /* Inverse of add: (a+b) - b = a */
    uint64_t a = 123456789ULL, b = 987654321ULL;
    TEST_EQ("sub(add(a,b), b) = a",
            goldilocks_sub(goldilocks_add(a, b), b), a);
}

static void test_field_mul(void) {
    printf("\n[Field Multiplication]\n");

    /* Basic: 3 * 7 = 21 */
    TEST_EQ("mul(3, 7) = 21", goldilocks_mul(3, 7), 21);

    /* Identity: a * 1 = a */
    TEST_EQ("mul(42, 1) = 42", goldilocks_mul(42, 1), 42);

    /* Zero: a * 0 = 0 */
    TEST_EQ("mul(42, 0) = 0", goldilocks_mul(42, 0), 0);

    /* Commutativity: a * b = b * a */
    TEST_EQ("mul(13, 17) = mul(17, 13)",
            goldilocks_mul(13, 17), goldilocks_mul(17, 13));

    /* (P-1) * (P-1) = 1 mod P  (since (-1)*(-1) = 1) */
    TEST_EQ("mul(P-1, P-1) = 1", goldilocks_mul(P - 1, P - 1), 1);

    /* (P-1) * 2 = P-2 mod P  (since -1 * 2 = -2) */
    TEST_EQ("mul(P-1, 2) = P-2", goldilocks_mul(P - 1, 2), P - 2);

    /* Large values: use Fermat: a^(P-1) = 1 for a != 0 */
    uint64_t a = 0x123456789ABCDEF0ULL % P;
    TEST_EQ("pow(a, P-1) = 1 (Fermat)", goldilocks_pow(a, P - 1), 1);
}

static void test_field_inv(void) {
    printf("\n[Field Inverse]\n");

    /* inv(1) = 1 */
    TEST_EQ("inv(1) = 1", goldilocks_inv(1), 1);

    /* inv(0) = 0 (sentinel) */
    TEST_EQ("inv(0) = 0 (sentinel)", goldilocks_inv(0), 0);

    /* a * inv(a) = 1 for small values */
    for (uint64_t a = 2; a <= 10; a++) {
        char name[64];
        snprintf(name, sizeof(name), "mul(%llu, inv(%llu)) = 1",
                 (unsigned long long)a, (unsigned long long)a);
        TEST_EQ(name, goldilocks_mul(a, goldilocks_inv(a)), 1);
    }

    /* inv(P-1) = P-1  (since (-1)^(-1) = -1) */
    TEST_EQ("inv(P-1) = P-1", goldilocks_inv(P - 1), P - 1);

    /* Large value roundtrip */
    uint64_t x = 0xDEADBEEFCAFE1234ULL % P;
    TEST_EQ("mul(x, inv(x)) = 1 (large)",
            goldilocks_mul(x, goldilocks_inv(x)), 1);
}

static void test_field_neg(void) {
    printf("\n[Field Negation]\n");

    /* neg(0) = 0 */
    TEST_EQ("neg(0) = 0", goldilocks_neg(0), 0);

    /* neg(1) = P-1 */
    TEST_EQ("neg(1) = P-1", goldilocks_neg(1), P - 1);

    /* a + neg(a) = 0 */
    uint64_t a = 42;
    TEST_EQ("add(a, neg(a)) = 0",
            goldilocks_add(a, goldilocks_neg(a)), 0);

    /* neg(P-1) = 1 */
    TEST_EQ("neg(P-1) = 1", goldilocks_neg(P - 1), 1);
}

static void test_field_sbox(void) {
    printf("\n[S-Box (x^7)]\n");

    /* sbox(0) = 0 */
    TEST_EQ("sbox(0) = 0", goldilocks_sbox(0), 0);

    /* sbox(1) = 1 (1^7 = 1) */
    TEST_EQ("sbox(1) = 1", goldilocks_sbox(1), 1);

    /* sbox(2) = 128 (2^7 = 128) */
    TEST_EQ("sbox(2) = 128", goldilocks_sbox(2), 128);

    /* sbox_inv(sbox(x)) = x roundtrip */
    uint64_t x = 42;
    TEST_EQ("sbox_inv(sbox(42)) = 42",
            goldilocks_sbox_inv(goldilocks_sbox(x)), x);

    /* sbox(sbox_inv(x)) = x roundtrip */
    x = 0xABCDEF0123456789ULL % P;
    TEST_EQ("sbox(sbox_inv(x)) = x (large)",
            goldilocks_sbox(goldilocks_sbox_inv(x)), x);
}

/*===========================================================================
 * 2. NTT Roundtrip Tests
 *===========================================================================*/

/* Primitive 8th root of unity for Goldilocks (from oracle_test.c) */
#define OMEGA_8   0xFFFFFFFEFF000001ULL
/* Modular inverse of 8: 8^(-1) mod P */
#define N_INV_8   0xDFFFFFFF20000001ULL

static void test_ntt_roundtrip_8(void) {
    printf("\n[NTT Roundtrip N=8]\n");

    goldilocks_t input[8] = {1, 2, 3, 4, 5, 6, 7, 8};
    goldilocks_t data[8];
    memcpy(data, input, sizeof(data));

    /* Forward NTT */
    int rc = ntt_forward(data, 8, OMEGA_8);
    TEST("ntt_forward returns 0", rc == 0);

    /* NTT output should differ from input (not identity) */
    int differs = 0;
    for (int i = 0; i < 8; i++) {
        if (data[i] != input[i]) { differs = 1; break; }
    }
    TEST("NTT output differs from input", differs);

    /* Inverse NTT */
    rc = ntt_inverse(data, 8, OMEGA_8, N_INV_8);
    TEST("ntt_inverse returns 0", rc == 0);

    /* Roundtrip: INTT(NTT(x)) = x */
    int match = 1;
    for (int i = 0; i < 8; i++) {
        if (data[i] != input[i]) { match = 0; break; }
    }
    TEST("INTT(NTT(x)) = x for [1..8]", match);
}

static void test_ntt_roundtrip_zero(void) {
    printf("\n[NTT Roundtrip Zero Vector]\n");

    goldilocks_t data[8] = {0, 0, 0, 0, 0, 0, 0, 0};

    int rc = ntt_forward(data, 8, OMEGA_8);
    TEST("ntt_forward(zeros) returns 0", rc == 0);

    /* NTT of zeros = zeros */
    int all_zero = 1;
    for (int i = 0; i < 8; i++) {
        if (data[i] != 0) { all_zero = 0; break; }
    }
    TEST("NTT(zeros) = zeros", all_zero);
}

static void test_ntt_roundtrip_single(void) {
    printf("\n[NTT Roundtrip Single Element]\n");

    goldilocks_t data[8] = {42, 0, 0, 0, 0, 0, 0, 0};
    goldilocks_t saved[8];
    memcpy(saved, data, sizeof(data));

    ntt_forward(data, 8, OMEGA_8);
    ntt_inverse(data, 8, OMEGA_8, N_INV_8);

    int match = 1;
    for (int i = 0; i < 8; i++) {
        if (data[i] != saved[i]) { match = 0; break; }
    }
    TEST("INTT(NTT([42,0,...,0])) = [42,0,...,0]", match);
}

static void test_ntt_linearity(void) {
    printf("\n[NTT Linearity]\n");

    /* NTT(a + b) = NTT(a) + NTT(b) */
    goldilocks_t a[8] = {1, 0, 3, 0, 5, 0, 7, 0};
    goldilocks_t b[8] = {0, 2, 0, 4, 0, 6, 0, 8};
    goldilocks_t sum_input[8];
    for (int i = 0; i < 8; i++) {
        sum_input[i] = goldilocks_add(a[i], b[i]);
    }

    /* NTT(a), NTT(b), NTT(a+b) */
    goldilocks_t ntt_a[8], ntt_b[8], ntt_sum[8];
    memcpy(ntt_a, a, sizeof(a));
    memcpy(ntt_b, b, sizeof(b));
    memcpy(ntt_sum, sum_input, sizeof(sum_input));

    ntt_forward(ntt_a, 8, OMEGA_8);
    ntt_forward(ntt_b, 8, OMEGA_8);
    ntt_forward(ntt_sum, 8, OMEGA_8);

    /* Check NTT(a+b) = NTT(a) + NTT(b) pointwise */
    int linear = 1;
    for (int i = 0; i < 8; i++) {
        if (ntt_sum[i] != goldilocks_add(ntt_a[i], ntt_b[i])) {
            linear = 0;
            break;
        }
    }
    TEST("NTT(a+b) = NTT(a) + NTT(b)", linear);
}

static void test_ntt_error_cases(void) {
    printf("\n[NTT Error Cases]\n");

    goldilocks_t data[4] = {1, 2, 3, 4};

    /* n=0 should fail */
    TEST("ntt_forward(n=0) fails", ntt_forward(data, 0, OMEGA_8) != 0);

    /* n=3 (not power of 2) should fail */
    TEST("ntt_forward(n=3) fails", ntt_forward(data, 3, OMEGA_8) != 0);
}

/*===========================================================================
 * 3. Poseidon2 (skipped — requires external BN254 constants)
 *===========================================================================*/

static void test_poseidon2(void) {
    printf("\n[Poseidon2]\n");
    printf("  SKIP: Poseidon2 headers use BN254 with external constants.\n");
    printf("        Standalone test not possible without linking constants.\n");
}

/*===========================================================================
 * Main
 *===========================================================================*/

int main(void) {
    printf("=========================================================\n");
    printf("  AMO-Lean Comprehensive Interoperability Tests (B94)\n");
    printf("  Goldilocks: P = 0x%016llx\n", (unsigned long long)P);
    printf("=========================================================\n");

    /* 1. Field arithmetic */
    test_field_add();
    test_field_sub();
    test_field_mul();
    test_field_inv();
    test_field_neg();
    test_field_sbox();

    /* 2. NTT roundtrip */
    test_ntt_roundtrip_8();
    test_ntt_roundtrip_zero();
    test_ntt_roundtrip_single();
    test_ntt_linearity();
    test_ntt_error_cases();

    /* 3. Poseidon2 */
    test_poseidon2();

    /* Summary */
    printf("\n=========================================================\n");
    printf("  Results: %d/%d passed", tests_passed, tests_run);
    if (tests_failed > 0) {
        printf(", %d FAILED", tests_failed);
    }
    printf("\n=========================================================\n");

    return tests_failed > 0 ? 1 : 0;
}
