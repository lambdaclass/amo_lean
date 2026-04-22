#!/usr/bin/env bash
set -euo pipefail

# Integration test: generate DFT_N with trzk, compile, and verify
# against the reference Walsh-Hadamard Transform implementation.
#
# Usage: ./integration_tests/run.sh --size N [--fuzz] [-n COUNT]
# (must be run from the project root)
#
# --size N     transform size. Required. Must be a registered size with a
#              matching dft${N}_spec.lean and test_vectors/wht${N}/ directory.
# --fuzz       drive the verifier with the random generator instead of the
#              crafted vectors (exit on first mismatch).
# -n COUNT     number of fuzz cases (default: unbounded, endless stream).
#
# Registered sizes (must match dft${N}_spec.lean and test_vectors/wht${N}/):
SIZES=(2 4)

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TRZK="$PROJECT_ROOT/.lake/build/bin/trzk"

FUZZ=0
FUZZ_COUNT=""
SIZE=""
while [ $# -gt 0 ]; do
    case "$1" in
        --fuzz) FUZZ=1; shift ;;
        --size) SIZE="$2"; shift 2 ;;
        --size=*) SIZE="${1#--size=}"; shift ;;
        -n) FUZZ_COUNT="$2"; shift 2 ;;
        -n=*) FUZZ_COUNT="${1#-n=}"; shift ;;
        *) echo "Unknown arg: $1" >&2; exit 2 ;;
    esac
done

if [ -z "$SIZE" ]; then
    echo "--size is required. Registered sizes: ${SIZES[*]}" >&2
    exit 2
fi

found=0
for s in "${SIZES[@]}"; do
    if [ "$s" = "$SIZE" ]; then found=1; fi
done
if [ "$found" -eq 0 ]; then
    echo "Unknown --size $SIZE. Registered sizes: ${SIZES[*]}" >&2
    exit 2
fi

N="$SIZE"
SPEC="$SCRIPT_DIR/dft${N}_spec.lean"
GEN_C="$SCRIPT_DIR/dft${N}_spec.c"
BIN="$SCRIPT_DIR/dft${N}"
VECTORS_DIR="$SCRIPT_DIR/test_vectors/wht${N}"

echo "=== Integration Test: DFT_${N} via trzk compiler driver ==="
echo ""

# 1. Build trzk if needed
if [ ! -f "$TRZK" ]; then
    echo "Building trzk..."
    (cd "$PROJECT_ROOT" && lake build trzk)
fi

# 2. Generate C from spec
echo "Generating C code from dft${N}_spec.lean..."
"$TRZK" "$SPEC" --target c --name "dft${N}" --output "$GEN_C"

# 3. Compile with parametric harness
echo "Compiling..."
clang -O2 -DN="$N" -DKERNEL="dft${N}" \
    -o "$BIN" "$GEN_C" "$SCRIPT_DIR/harness.c"

# 4. Verify
echo "Verifying..."
RESULT=0
if [ "$FUZZ" -eq 1 ]; then
    if [ -n "$FUZZ_COUNT" ]; then
        uv run "$SCRIPT_DIR/generators/wht.py" --size "$N" -n "$FUZZ_COUNT" \
            | python3 "$SCRIPT_DIR/verify_dft.py" --binary "$BIN" --size "$N" --fuzz \
            || RESULT=$?
    else
        uv run "$SCRIPT_DIR/generators/wht.py" --size "$N" \
            | python3 "$SCRIPT_DIR/verify_dft.py" --binary "$BIN" --size "$N" --fuzz \
            || RESULT=$?
    fi
else
    cat "$VECTORS_DIR"/*.txt \
        | python3 "$SCRIPT_DIR/verify_dft.py" --binary "$BIN" --size "$N" \
        || RESULT=$?
fi

# 5. Clean up generated artifacts
rm -f "$GEN_C" "$BIN"
rm -rf "$SCRIPT_DIR/artifacts"

echo ""
if [ $RESULT -eq 0 ]; then
    echo "=== Integration test PASSED (size ${N}) ==="
else
    echo "=== Integration test FAILED (size ${N}) ==="
fi
exit $RESULT
