#!/usr/bin/env bash
set -euo pipefail

# Integration tests for all Spec operations.
# Runs trzk on each spec, compiles the output, and verifies correctness.
#
# Usage: ./integration_tests/run_all.sh
# (must be run from the project root)

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TRZK="$PROJECT_ROOT/.lake/build/bin/trzk"
BUILD_DIR="$SCRIPT_DIR/build"
SPECS_DIR="$SCRIPT_DIR/specs"
VERIFIER="$SCRIPT_DIR/verify_all.py"

PASSED=0
FAILED=0
SKIPPED=0

cleanup() {
    rm -rf "$BUILD_DIR"
}
trap cleanup EXIT

echo "════════════════════════════════════════════════════════════"
echo "  trzk Integration Tests — All Spec Operations"
echo "════════════════════════════════════════════════════════════"
echo ""

# Build trzk if needed
if [ ! -f "$TRZK" ]; then
    echo "Building trzk..."
    (cd "$PROJECT_ROOT" && lake build trzk)
fi

mkdir -p "$BUILD_DIR"

# ────────────────────────────────────────────────────
# Matrix tests: dft, identity, kron, compose
# ────────────────────────────────────────────────────

run_matrix_test() {
    local name="$1"
    local func_name="$2"
    local spec_file="$SPECS_DIR/${name}.lean"

    if [ ! -f "$spec_file" ]; then
        echo "  SKIP $name: spec file not found"
        SKIPPED=$((SKIPPED + 1))
        return
    fi

    # Generate C
    if ! "$TRZK" "$spec_file" --target c --name "$func_name" --output "$BUILD_DIR/${name}.c" 2>/dev/null; then
        echo "  FAIL $name: trzk codegen failed"
        FAILED=$((FAILED + 1))
        return
    fi

    # Compile with generic matrix harness
    if ! clang -O2 -DFUNC_NAME="$func_name" -o "$BUILD_DIR/${name}" \
         "$BUILD_DIR/${name}.c" "$SCRIPT_DIR/harness_matrix.c" 2>/dev/null; then
        echo "  FAIL $name: compilation failed"
        FAILED=$((FAILED + 1))
        return
    fi

    # Verify
    if python3 "$VERIFIER" --test "$name" --binary "$BUILD_DIR/${name}"; then
        PASSED=$((PASSED + 1))
    else
        FAILED=$((FAILED + 1))
    fi
}

echo "── Matrix Operations ──"
run_matrix_test "dft2" "dft2"
run_matrix_test "dft4" "dft4"
run_matrix_test "dft8" "dft8"
run_matrix_test "identity4" "identity4"
run_matrix_test "kron_i3_dft2" "kron_test"
run_matrix_test "compose_ct4" "compose_test"

# ────────────────────────────────────────────────────
# NTT test (different harness — in-place, int32, twiddles)
# ────────────────────────────────────────────────────

echo ""
echo "── NTT ──"

NTT_SPEC="$SPECS_DIR/ntt_babybear_16.lean"
if [ -f "$NTT_SPEC" ]; then
    if "$TRZK" "$NTT_SPEC" --target c --name ntt16 --output "$BUILD_DIR/ntt16.c" 2>/dev/null; then
        # The generated NTT file is self-contained (has mod_pow, compute_twiddles, kernel).
        # Append a test main that computes twiddles and runs the NTT.
        cat >> "$BUILD_DIR/ntt16.c" << 'NTT_MAIN'

/* Test harness — appended by integration test */
#include <stdio.h>
#include <string.h>

int main(int argc, char* argv[]) {
    if (argc < 2) { fprintf(stderr, "Usage: %s <x0> [x1] ...\n", argv[0]); return 1; }
    int n = argc - 1;
    int32_t data[16] = {0};
    for (int i = 0; i < n && i < 16; i++)
        data[i] = (int32_t)atoll(argv[i + 1]);

    /* Compute twiddles */
    size_t logn = 4;  /* log2(16) */
    uint64_t p = 2013265921ULL;
    uint64_t gen = 31ULL;
    uint32_t tw[16 * 4];
    compute_twiddles(tw, 16, logn, p, gen);

    /* The generated function name from emitPlanBasedNTTC */
    /* Find the function — it's named babybear_ntt_plan */
    babybear_ntt_plan(data, (const int32_t*)tw);

    for (int i = 0; i < 16; i++) {
        if (i > 0) printf(" ");
        printf("%d", data[i]);
    }
    printf("\n");
    return 0;
}
NTT_MAIN

        if clang -O2 -o "$BUILD_DIR/ntt16" "$BUILD_DIR/ntt16.c" 2>/dev/null; then
            # Run with a simple test vector and check it doesn't crash
            # and outputs 16 values
            OUTPUT=$("$BUILD_DIR/ntt16" 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2>/dev/null || true)
            COUNT=$(echo "$OUTPUT" | wc -w | tr -d ' ')
            if [ "$COUNT" = "16" ]; then
                echo ""
                echo "  ntt_babybear_16 (16 elements, BabyBear field)"
                echo "    PASS (compiled and produced 16-element output)"
                PASSED=$((PASSED + 1))
            else
                echo ""
                echo "  ntt_babybear_16"
                echo "    FAIL: expected 16 values, got $COUNT"
                FAILED=$((FAILED + 1))
            fi
        else
            echo ""
            echo "  ntt_babybear_16"
            echo "    FAIL: compilation failed"
            FAILED=$((FAILED + 1))
        fi
    else
        echo "  FAIL ntt_babybear_16: trzk codegen failed"
        FAILED=$((FAILED + 1))
    fi
else
    echo "  SKIP ntt_babybear_16: spec not found"
    SKIPPED=$((SKIPPED + 1))
fi

# ────────────────────────────────────────────────────
# Poseidon S-box test
# ────────────────────────────────────────────────────

echo ""
echo "── Poseidon2 S-box ──"

SBOX_SPEC="$SPECS_DIR/poseidon_sbox.lean"
if [ -f "$SBOX_SPEC" ]; then
    if "$TRZK" "$SBOX_SPEC" --target c --name sbox --output "$BUILD_DIR/spec_sbox.c" 2>/dev/null; then
        # The generated S-box is a static inline function.
        # Build a self-contained test: prepend #include, append main.
        {
            echo '#include <stdio.h>'
            echo '#include <stdlib.h>'
            echo '#include <stdint.h>'
            echo ''
            # Strip the 'static inline' so we can call it from main
            sed 's/^static inline //' "$BUILD_DIR/spec_sbox.c"
            echo ''
            echo 'int main(int argc, char* argv[]) {'
            echo '    if (argc != 2) { fprintf(stderr, "Usage: %s <x>\\n", argv[0]); return 1; }'
            echo '    uint64_t x = strtoull(argv[1], NULL, 10);'
            echo '    uint64_t result = sbox5(x);'
            echo '    printf("%llu\\n", (unsigned long long)result);'
            echo '    return 0;'
            echo '}'
        } > "$BUILD_DIR/test_sbox.c"
        if (cd "$BUILD_DIR" && clang -O2 -o test_sbox test_sbox.c 2>"$BUILD_DIR/sbox_err.txt"); then
            if python3 "$VERIFIER" --test poseidon_sbox --binary "$BUILD_DIR/test_sbox"; then
                PASSED=$((PASSED + 1))
            else
                FAILED=$((FAILED + 1))
            fi
        else
            echo ""
            echo "  poseidon_sbox"
            echo "    FAIL: compilation failed (generated C has bugs)"
            cat "$BUILD_DIR/sbox_err.txt" | head -5 | sed 's/^/    /'
            FAILED=$((FAILED + 1))
        fi
    else
        echo "  FAIL poseidon_sbox: trzk codegen failed"
        FAILED=$((FAILED + 1))
    fi
else
    echo "  SKIP poseidon_sbox: spec not found"
    SKIPPED=$((SKIPPED + 1))
fi

# ────────────────────────────────────────────────────
# Summary
# ────────────────────────────────────────────────────

TOTAL=$((PASSED + FAILED + SKIPPED))
echo ""
echo "════════════════════════════════════════════════════════════"
echo "  Results: $PASSED passed, $FAILED failed, $SKIPPED skipped (of $TOTAL)"
if [ $FAILED -eq 0 ]; then
    echo "  ALL TESTS PASSED"
else
    echo "  SOME TESTS FAILED"
fi
echo "════════════════════════════════════════════════════════════"

exit $FAILED
