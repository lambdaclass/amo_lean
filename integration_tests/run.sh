#!/usr/bin/env bash
set -euo pipefail

# Integration test: generate DFT_4 with trzk, compile, and verify
# against the reference Walsh-Hadamard Transform implementation.
#
# Usage: ./integration_tests/run.sh
# (must be run from the project root)

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TRZK="$PROJECT_ROOT/.lake/build/bin/trzk"

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

# 4. Verify against reference
echo "Verifying against Walsh-Hadamard reference..."
python3 "$SCRIPT_DIR/verify_dft4.py" --binary "$SCRIPT_DIR/dft4" "$SCRIPT_DIR/test_vectors.txt"
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
