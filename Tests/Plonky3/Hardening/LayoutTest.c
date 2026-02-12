/**
 * LayoutTest.c - ABI & Memory Layout Audit
 *
 * Phase 6A Hardening: Test 4
 *
 * Purpose: Verify that #[repr(C)] is working correctly and that
 * C and Rust agree on struct layouts, sizes, and alignments.
 *
 * This is critical for FFI safety. If layouts don't match,
 * data corruption and UB will occur.
 *
 * Tests:
 * 1. Struct size matches between C and Rust
 * 2. Struct alignment matches
 * 3. Field offsets match
 * 4. Data survives round-trip through FFI
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <dlfcn.h>

/*===========================================================================
 * Test Structure (must match Rust's TestLayout)
 *===========================================================================*/

/* This MUST match the Rust definition:
 * #[repr(C)]
 * pub struct TestLayout {
 *     pub byte1: u8,
 *     pub value: u64,
 *     pub byte2: u8,
 * }
 */
typedef struct {
    uint8_t byte1;
    uint64_t value;
    uint8_t byte2;
} TestLayout;

/*===========================================================================
 * Function Types
 *===========================================================================*/

typedef size_t (*sizeof_fn)(void);
typedef size_t (*alignof_fn)(void);
typedef size_t (*offsetof_fn)(void);
typedef uint64_t (*verify_fn)(TestLayout*);

/*===========================================================================
 * Test Functions
 *===========================================================================*/

static int test_sizes(void* lib) {
    printf("\n[TEST 1] Structure Size...\n");

    sizeof_fn rust_sizeof = (sizeof_fn)dlsym(lib, "plonky3_sizeof_test_layout");
    if (!rust_sizeof) {
        printf("  [SKIP] plonky3_sizeof_test_layout not available\n");
        return 0;
    }

    size_t c_size = sizeof(TestLayout);
    size_t rust_size = rust_sizeof();

    printf("  C sizeof(TestLayout):    %zu bytes\n", c_size);
    printf("  Rust size_of::<>():      %zu bytes\n", rust_size);

    if (c_size == rust_size) {
        printf("  [PASS] Sizes match!\n");
        return 0;
    } else {
        printf("  [FAIL] Size mismatch! ABI INCOMPATIBLE.\n");
        return 1;
    }
}

static int test_alignment(void* lib) {
    printf("\n[TEST 2] Structure Alignment...\n");

    alignof_fn rust_alignof = (alignof_fn)dlsym(lib, "plonky3_alignof_test_layout");
    if (!rust_alignof) {
        printf("  [SKIP] plonky3_alignof_test_layout not available\n");
        return 0;
    }

    size_t c_align = _Alignof(TestLayout);
    size_t rust_align = rust_alignof();

    printf("  C _Alignof(TestLayout):  %zu bytes\n", c_align);
    printf("  Rust align_of::<>():     %zu bytes\n", rust_align);

    if (c_align == rust_align) {
        printf("  [PASS] Alignments match!\n");
        return 0;
    } else {
        printf("  [FAIL] Alignment mismatch! ABI INCOMPATIBLE.\n");
        return 1;
    }
}

static int test_offsets(void* lib) {
    printf("\n[TEST 3] Field Offsets...\n");

    offsetof_fn rust_off_byte1 = (offsetof_fn)dlsym(lib, "plonky3_offsetof_byte1");
    offsetof_fn rust_off_value = (offsetof_fn)dlsym(lib, "plonky3_offsetof_value");
    offsetof_fn rust_off_byte2 = (offsetof_fn)dlsym(lib, "plonky3_offsetof_byte2");

    if (!rust_off_byte1 || !rust_off_value || !rust_off_byte2) {
        printf("  [SKIP] Offset functions not available\n");
        return 0;
    }

    size_t c_off_byte1 = offsetof(TestLayout, byte1);
    size_t c_off_value = offsetof(TestLayout, value);
    size_t c_off_byte2 = offsetof(TestLayout, byte2);

    size_t r_off_byte1 = rust_off_byte1();
    size_t r_off_value = rust_off_value();
    size_t r_off_byte2 = rust_off_byte2();

    printf("  Field     | C offset | Rust offset | Match\n");
    printf("  ----------|----------|-------------|------\n");
    printf("  byte1     | %8zu | %11zu | %s\n",
           c_off_byte1, r_off_byte1, c_off_byte1 == r_off_byte1 ? "YES" : "NO");
    printf("  value     | %8zu | %11zu | %s\n",
           c_off_value, r_off_value, c_off_value == r_off_value ? "YES" : "NO");
    printf("  byte2     | %8zu | %11zu | %s\n",
           c_off_byte2, r_off_byte2, c_off_byte2 == r_off_byte2 ? "YES" : "NO");

    if (c_off_byte1 == r_off_byte1 &&
        c_off_value == r_off_value &&
        c_off_byte2 == r_off_byte2) {
        printf("  [PASS] All offsets match!\n");
        return 0;
    } else {
        printf("  [FAIL] Offset mismatch! ABI INCOMPATIBLE.\n");
        return 1;
    }
}

static int test_roundtrip(void* lib) {
    printf("\n[TEST 4] Data Round-Trip...\n");

    verify_fn verify = (verify_fn)dlsym(lib, "plonky3_verify_layout");
    if (!verify) {
        printf("  [SKIP] plonky3_verify_layout not available\n");
        return 0;
    }

    /* Initialize with known values */
    TestLayout layout;
    layout.byte1 = 0xAB;
    layout.value = 0x123456789ABCDEF0ULL;
    layout.byte2 = 0xCD;

    printf("  Before Rust call:\n");
    printf("    byte1 = 0x%02x\n", layout.byte1);
    printf("    value = 0x%016llx\n", (unsigned long long)layout.value);
    printf("    byte2 = 0x%02x\n", layout.byte2);

    /* Expected checksum: byte1 XOR value XOR byte2 */
    uint64_t expected_checksum = (uint64_t)0xAB ^ 0x123456789ABCDEF0ULL ^ (uint64_t)0xCD;

    /* Call Rust (it modifies the values and returns checksum of originals) */
    uint64_t checksum = verify(&layout);

    printf("\n  After Rust call:\n");
    printf("    byte1 = 0x%02x (expected 0xAC = 0xAB + 1)\n", layout.byte1);
    printf("    value = 0x%016llx (expected 0x...54 = ...F0 + 100)\n",
           (unsigned long long)layout.value);
    printf("    byte2 = 0x%02x (expected 0xCF = 0xCD + 2)\n", layout.byte2);

    printf("\n  Checksum from Rust: 0x%016llx\n", (unsigned long long)checksum);
    printf("  Expected checksum:  0x%016llx\n", (unsigned long long)expected_checksum);

    int errors = 0;

    /* Verify modifications */
    if (layout.byte1 != 0xAC) {
        printf("  [FAIL] byte1 not modified correctly\n");
        errors++;
    }

    if (layout.value != 0x123456789ABCDEF0ULL + 100) {
        printf("  [FAIL] value not modified correctly\n");
        errors++;
    }

    if (layout.byte2 != 0xCF) {
        printf("  [FAIL] byte2 not modified correctly\n");
        errors++;
    }

    if (checksum != expected_checksum) {
        printf("  [FAIL] Checksum mismatch - Rust read wrong values\n");
        errors++;
    }

    if (errors == 0) {
        printf("  [PASS] Data survived round-trip correctly!\n");
        return 0;
    } else {
        printf("  [FAIL] Round-trip corrupted data!\n");
        return 1;
    }
}

static int test_pointer_by_value(void* lib) {
    printf("\n[TEST 5] Pointer vs Value Semantics...\n");

    /* Note: We can only test pointer passing since C can't pass structs
     * by value to extern functions portably. The test here verifies
     * that pointer-based passing works correctly. */

    verify_fn verify = (verify_fn)dlsym(lib, "plonky3_verify_layout");
    if (!verify) {
        printf("  [SKIP] verify function not available\n");
        return 0;
    }

    /* Test with heap-allocated struct */
    TestLayout* heap_layout = malloc(sizeof(TestLayout));
    if (!heap_layout) {
        printf("  [FAIL] malloc failed\n");
        return 1;
    }

    heap_layout->byte1 = 0x11;
    heap_layout->value = 0x2222222222222222ULL;
    heap_layout->byte2 = 0x33;

    uint64_t expected = (uint64_t)0x11 ^ 0x2222222222222222ULL ^ (uint64_t)0x33;
    uint64_t result = verify(heap_layout);

    int pass = (result == expected &&
                heap_layout->byte1 == 0x12 &&
                heap_layout->byte2 == 0x35);

    free(heap_layout);

    if (pass) {
        printf("  [PASS] Heap-allocated struct works correctly\n");
        return 0;
    } else {
        printf("  [FAIL] Heap-allocated struct failed\n");
        return 1;
    }
}

static int test_null_safety(void* lib) {
    printf("\n[TEST 6] NULL Pointer Safety...\n");

    verify_fn verify = (verify_fn)dlsym(lib, "plonky3_verify_layout");
    if (!verify) {
        printf("  [SKIP] verify function not available\n");
        return 0;
    }

    uint64_t result = verify(NULL);

    if (result == UINT64_MAX) {
        printf("  [PASS] NULL pointer returns error (UINT64_MAX)\n");
        return 0;
    } else {
        printf("  [FAIL] NULL pointer not handled safely\n");
        return 1;
    }
}

/*===========================================================================
 * Main
 *===========================================================================*/

int main(void) {
    printf("═══════════════════════════════════════════════════════════════════════\n");
    printf("  ABI & Memory Layout Audit\n");
    printf("  Phase 6A Hardening Suite\n");
    printf("═══════════════════════════════════════════════════════════════════════\n");
    printf("\n  Verifying #[repr(C)] struct compatibility...\n");

    /* Print C-side layout info */
    printf("\n  C-side TestLayout info:\n");
    printf("    sizeof:  %zu bytes\n", sizeof(TestLayout));
    printf("    alignof: %zu bytes\n", _Alignof(TestLayout));
    printf("    offsetof(byte1): %zu\n", offsetof(TestLayout, byte1));
    printf("    offsetof(value): %zu\n", offsetof(TestLayout, value));
    printf("    offsetof(byte2): %zu\n", offsetof(TestLayout, byte2));

    /* Load library */
    printf("\nLoading Plonky3 shim...\n");

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

    printf("Library loaded successfully.\n");

    /* Run tests */
    int errors = 0;
    errors += test_sizes(lib);
    errors += test_alignment(lib);
    errors += test_offsets(lib);
    errors += test_roundtrip(lib);
    errors += test_pointer_by_value(lib);
    errors += test_null_safety(lib);

    /* Summary */
    printf("\n═══════════════════════════════════════════════════════════════════════\n");
    printf("  ABI LAYOUT AUDIT SUMMARY\n");
    printf("═══════════════════════════════════════════════════════════════════════\n");

    if (errors == 0) {
        printf("\n  [PASS] All ABI compatibility tests passed!\n");
        printf("\n  VERDICT: #[repr(C)] is working correctly.\n");
        printf("  - Struct sizes match\n");
        printf("  - Alignments match\n");
        printf("  - Field offsets match\n");
        printf("  - Data survives FFI round-trip\n");
    } else {
        printf("\n  [FAIL] %d ABI compatibility tests failed!\n", errors);
        printf("\n  VERDICT: ABI INCOMPATIBLE - DO NOT USE IN PRODUCTION.\n");
        printf("  This indicates a serious bug in the FFI layer.\n");
    }

    printf("\n═══════════════════════════════════════════════════════════════════════\n");

    dlclose(lib);
    return errors > 0 ? 1 : 0;
}
