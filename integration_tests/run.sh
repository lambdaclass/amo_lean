#!/usr/bin/env bash
set -euo pipefail

# Integration test: compile arith_spec_${N} with trzk, link with the Rust
# harness, and verify against reference vectors.
#
# Usage: ./integration_tests/run.sh --size N [--fuzz] [-n COUNT]
# (run from project root)

SIZES=(1)

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
SPEC="$SCRIPT_DIR/arith_spec_${N}.lean"
GEN_RS="$SCRIPT_DIR/generated.rs"
BIN="/tmp/arith_${N}"
VECTORS_DIR="$SCRIPT_DIR/test_vectors/arith_${N}"

echo "=== Integration Test: arith_spec_${N} via trzk ==="

# 1. Build unconditionally (cheap when up-to-date). `lake build` resolves to
# defaultTargets (TRZK, Tests, trzk); we need the TRZK lib oleans on disk
# because the trzk runner re-elaborates a temp file via `lake env lean --run`.
(cd "$PROJECT_ROOT" && lake build)

# 2. Generate Rust from spec.
echo "Generating Rust from arith_spec_${N}.lean..."
"$TRZK" "$SPEC" --name "arith_spec" --output "$GEN_RS"

# 3. Compile harness (which #[path]s the generated file).
echo "Compiling..."
rustc -O --edition 2024 "$SCRIPT_DIR/harness.rs" -o "$BIN"

# 4. Verify.
RESULT=0
if [ "$FUZZ" -eq 1 ]; then
    if [ -n "$FUZZ_COUNT" ]; then
        python3 "$SCRIPT_DIR/generators/arith.py" --arity "$N" -n "$FUZZ_COUNT" \
            | python3 "$SCRIPT_DIR/verify_arith.py" --binary "$BIN" --arity "$N" --fuzz \
            || RESULT=$?
    else
        python3 "$SCRIPT_DIR/generators/arith.py" --arity "$N" \
            | python3 "$SCRIPT_DIR/verify_arith.py" --binary "$BIN" --arity "$N" --fuzz \
            || RESULT=$?
    fi
else
    cat "$VECTORS_DIR"/*.txt \
        | python3 "$SCRIPT_DIR/verify_arith.py" --binary "$BIN" --arity "$N" \
        || RESULT=$?
fi

# 5. Cleanup.
rm -f "$GEN_RS" "$BIN"
rm -rf "$SCRIPT_DIR/artifacts"

if [ $RESULT -eq 0 ]; then
    echo "=== Integration test PASSED (size ${N}) ==="
else
    echo "=== Integration test FAILED (size ${N}) ==="
fi
exit $RESULT
