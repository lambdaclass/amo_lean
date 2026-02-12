/**
 * shim_test.c - Basic test for plonky3_shim loading
 *
 * Verifies that the Rust shim can be loaded dynamically from C
 * and that basic functions work correctly.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <dlfcn.h>

/* Function pointer types */
typedef uint64_t (*get_prime_fn)(void);
typedef uint64_t (*get_omega_fn)(size_t);
typedef int (*is_montgomery_fn)(void);
typedef int (*ntt_fn)(uint64_t*, size_t);
typedef uint64_t (*field_op_fn)(uint64_t, uint64_t);
typedef uint32_t (*version_fn)(void);

/* Expected Goldilocks prime */
#define GOLDILOCKS_PRIME 0xFFFFFFFF00000001ULL

/* Test result tracking */
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name, condition) do { \
    if (condition) { \
        printf("  [PASS] %s\n", name); \
        tests_passed++; \
    } else { \
        printf("  [FAIL] %s\n", name); \
        tests_failed++; \
    } \
} while(0)

int main(void) {
    printf("═══════════════════════════════════════════════════════════\n");
    printf("  Plonky3 Shim Loading Test\n");
    printf("  Phase 6A.2: FFI Verification\n");
    printf("═══════════════════════════════════════════════════════════\n\n");

    /* Load the shared library */
    printf("Loading libplonky3_shim...\n");

#ifdef __APPLE__
    const char* lib_path = "./plonky3_shim/target/release/libplonky3_shim.dylib";
#else
    const char* lib_path = "./plonky3_shim/target/release/libplonky3_shim.so";
#endif

    void* lib = dlopen(lib_path, RTLD_NOW);
    if (!lib) {
        fprintf(stderr, "ERROR: Failed to load library: %s\n", dlerror());
        return 1;
    }
    printf("Library loaded successfully.\n\n");

    /* Load function pointers */
    get_prime_fn get_prime = (get_prime_fn)dlsym(lib, "plonky3_goldilocks_prime");
    get_omega_fn get_omega = (get_omega_fn)dlsym(lib, "plonky3_get_omega");
    is_montgomery_fn is_montgomery = (is_montgomery_fn)dlsym(lib, "plonky3_is_montgomery");
    ntt_fn ntt_forward = (ntt_fn)dlsym(lib, "plonky3_ntt_forward");
    ntt_fn ntt_inverse = (ntt_fn)dlsym(lib, "plonky3_ntt_inverse");
    field_op_fn add = (field_op_fn)dlsym(lib, "plonky3_add");
    field_op_fn mul = (field_op_fn)dlsym(lib, "plonky3_mul");
    field_op_fn sub = (field_op_fn)dlsym(lib, "plonky3_sub");
    version_fn version = (version_fn)dlsym(lib, "plonky3_shim_version");

    /* Verify all symbols loaded */
    printf("=== Symbol Loading ===\n");
    TEST("plonky3_goldilocks_prime", get_prime != NULL);
    TEST("plonky3_get_omega", get_omega != NULL);
    TEST("plonky3_is_montgomery", is_montgomery != NULL);
    TEST("plonky3_ntt_forward", ntt_forward != NULL);
    TEST("plonky3_ntt_inverse", ntt_inverse != NULL);
    TEST("plonky3_add", add != NULL);
    TEST("plonky3_mul", mul != NULL);
    TEST("plonky3_sub", sub != NULL);
    TEST("plonky3_shim_version", version != NULL);

    if (tests_failed > 0) {
        printf("\nERROR: Some symbols failed to load. Aborting.\n");
        dlclose(lib);
        return 1;
    }

    /* Test basic functions */
    printf("\n=== Basic Function Tests ===\n");

    /* Prime value */
    uint64_t prime = get_prime();
    TEST("Prime value correct", prime == GOLDILOCKS_PRIME);
    printf("       Prime = 0x%llx\n", (unsigned long long)prime);

    /* Montgomery check */
    int mont = is_montgomery();
    TEST("Not Montgomery representation", mont == 0);

    /* Version */
    uint32_t ver = version();
    TEST("Version is 0.1.0 (100)", ver == 100);

    /* Omega values (must match AMO-Lean) */
    printf("\n=== Omega Value Tests ===\n");
    TEST("omega_256 (log=8)", get_omega(8) == 0xbf79143ce60ca966ULL);
    TEST("omega_1024 (log=10)", get_omega(10) == 0x9d8f2ad78bfed972ULL);
    TEST("omega_4096 (log=12)", get_omega(12) == 0xf2c35199959dfcb6ULL);
    TEST("omega_16384 (log=14)", get_omega(14) == 0xe0ee099310bba1e2ULL);

    printf("       omega_256  = 0x%llx\n", (unsigned long long)get_omega(8));
    printf("       omega_1024 = 0x%llx\n", (unsigned long long)get_omega(10));

    /* Field arithmetic */
    printf("\n=== Field Arithmetic Tests ===\n");
    TEST("1 + 2 = 3", add(1, 2) == 3);
    TEST("2 * 3 = 6", mul(2, 3) == 6);
    TEST("5 - 3 = 2", sub(5, 3) == 2);
    TEST("(p-1) + 2 = 1 (mod p)", add(prime - 1, 2) == 1);
    TEST("0 - 1 = p-1 (mod p)", sub(0, 1) == prime - 1);

    /* NTT roundtrip */
    printf("\n=== NTT Roundtrip Test ===\n");
    uint64_t data[8] = {1, 2, 3, 4, 5, 6, 7, 8};
    uint64_t original[8];
    memcpy(original, data, sizeof(data));

    int ret = ntt_forward(data, 8);
    TEST("NTT forward returns 0", ret == 0);

    /* Check that data changed */
    int changed = 0;
    for (int i = 0; i < 8; i++) {
        if (data[i] != original[i]) changed = 1;
    }
    TEST("NTT changed the data", changed == 1);

    ret = ntt_inverse(data, 8);
    TEST("NTT inverse returns 0", ret == 0);

    /* Check roundtrip */
    int match = 1;
    for (int i = 0; i < 8; i++) {
        if (data[i] != original[i]) match = 0;
    }
    TEST("INTT(NTT(x)) = x", match == 1);

    /* Print NTT result for reference */
    printf("\n=== NTT Result (N=8) ===\n");
    memcpy(data, original, sizeof(data));
    ntt_forward(data, 8);
    printf("       Input:  [");
    for (int i = 0; i < 8; i++) printf("%llu%s", (unsigned long long)original[i], i<7?", ":"");
    printf("]\n");
    printf("       Output: [");
    for (int i = 0; i < 8; i++) printf("%llu%s", (unsigned long long)data[i], i<7?", ":"");
    printf("]\n");

    /* Error handling */
    printf("\n=== Error Handling Tests ===\n");
    TEST("NULL pointer returns -1", ntt_forward(NULL, 8) == -1);
    TEST("Non-power-of-2 returns -1", ntt_forward(data, 7) == -1);
    TEST("Zero length returns -1", ntt_forward(data, 0) == -1);

    /* Summary */
    printf("\n═══════════════════════════════════════════════════════════\n");
    printf("  RESULTS: %d passed, %d failed\n", tests_passed, tests_failed);
    printf("═══════════════════════════════════════════════════════════\n");

    dlclose(lib);
    return tests_failed > 0 ? 1 : 0;
}
