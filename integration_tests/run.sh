#!/usr/bin/env bash
set -euo pipefail

# Integration test: generate DFT_4 with trzk, compile, and verify
# against the reference Walsh-Hadamard Transform implementation.
#
# Usage: ./integration_tests/run.sh [--fuzz] [-n COUNT]
# (must be run from the project root)
#
# --fuzz       pass --fuzz to verify_dft4.py (exit on first mismatch), and
#              drive the verifier with the random generator instead of the
#              crafted vectors.
# -n COUNT     number of fuzz cases to generate (default 1000).

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TRZK="$PROJECT_ROOT/.lake/build/bin/trzk"

FUZZ=0
FUZZ_COUNT=1000
while [ $# -gt 0 ]; do
    case "$1" in
        --fuzz) FUZZ=1; shift ;;
        -n) FUZZ_COUNT="$2"; shift 2 ;;
        -n=*) FUZZ_COUNT="${1#-n=}"; shift ;;
        *) echo "Unknown arg: $1" >&2; exit 2 ;;
    esac
done

echo "=== Integration Test: DFT_4 via trzk compiler driver ==="
echo ""

# 1. Build trzk if needed
if [ ! -f "$TRZK" ]; then
    echo "Building trzk..."
    (cd "$PROJECT_ROOT" && lake build trzk)
fi

# 2. Generate C from spec
echo "Generating C code from dft4_spec.lean..."
"$TRZK" "$SCRIPT_DIR/dft4_spec.lean" --target c --name dft4 --output "$SCRIPT_DIR/dft4_spec.c"

# 3. Compile with harness
echo "Compiling..."
clang -O2 -o "$SCRIPT_DIR/dft4" "$SCRIPT_DIR/dft4_spec.c" "$SCRIPT_DIR/harness_4.c"

# 4. Verify against expected outputs in test_vectors.txt
echo "Verifying against test vectors..."
if [ "$FUZZ" -eq 1 ]; then
    uv run "$SCRIPT_DIR/generators/wht4.py" -n "$FUZZ_COUNT" \
        | python3 "$SCRIPT_DIR/verify_dft4.py" --binary "$SCRIPT_DIR/dft4" --fuzz
else
    cat "$SCRIPT_DIR"/test_vectors/wht4/*.txt \
        | python3 "$SCRIPT_DIR/verify_dft4.py" --binary "$SCRIPT_DIR/dft4"
fi
RESULT=$?

# 5. Clean up generated artifacts
rm -f "$SCRIPT_DIR/dft4_spec.c" "$SCRIPT_DIR/dft4"
rm -rf "$SCRIPT_DIR/artifacts"

echo ""
if [ $RESULT -eq 0 ]; then
    echo "=== Integration test PASSED ==="
else
    echo "=== Integration test FAILED ==="
fi
exit $RESULT
