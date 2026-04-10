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

run_ntt_test() {
    local name="$1"
    local func_name="$2"
    local size="$3"
    local logn="$4"
    local prime="$5"
    local gen="$6"
    local spec_file="$SPECS_DIR/${name}.lean"

    if [ ! -f "$spec_file" ]; then
        echo "  SKIP $name: spec file not found"
        SKIPPED=$((SKIPPED + 1))
        return
    fi

    if ! "$TRZK" "$spec_file" --target c --name "$func_name" --output "$BUILD_DIR/${name}.c" 2>/dev/null; then
        echo "  FAIL $name: trzk codegen failed"
        FAILED=$((FAILED + 1))
        return
    fi

    if ! clang -O2 \
         -DNTT_FUNC="$func_name" \
         -DNTT_SIZE="$size" \
         -DNTT_LOGN="$logn" \
         -DNTT_PRIME="${prime}" \
         -DNTT_GEN="${gen}" \
         -o "$BUILD_DIR/${name}" \
         "$BUILD_DIR/${name}.c" "$SCRIPT_DIR/harness_ntt.c" 2>/dev/null; then
        echo "  FAIL $name: compilation failed"
        FAILED=$((FAILED + 1))
        return
    fi

    # Verify against Python reference NTT
    if python3 "$VERIFIER" --test "$name" --binary "$BUILD_DIR/${name}"; then
        PASSED=$((PASSED + 1))
    else
        FAILED=$((FAILED + 1))
    fi
}

run_ntt_test "ntt_babybear_16" "babybear_ntt_plan" 16 4 "2013265921ULL" "31ULL"

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
