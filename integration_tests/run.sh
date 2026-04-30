#!/usr/bin/env bash
set -euo pipefail

# Integration test: compile arith_spec_${OP} with trzk, link with the Rust
# harness, and verify against reference vectors.
#
# Usage: ./integration_tests/run.sh --op OP [--fuzz] [-n COUNT]
# (run from project root)

OPS=(add0 mul idiv1 shl shr)

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TRZK="$PROJECT_ROOT/.lake/build/bin/trzk"

FUZZ=0
FUZZ_COUNT=""
OP=""
while [ $# -gt 0 ]; do
    case "$1" in
        --fuzz) FUZZ=1; shift ;;
        --op) OP="$2"; shift 2 ;;
        --op=*) OP="${1#--op=}"; shift ;;
        -n) FUZZ_COUNT="$2"; shift 2 ;;
        -n=*) FUZZ_COUNT="${1#-n=}"; shift ;;
        *) echo "Unknown arg: $1" >&2; exit 2 ;;
    esac
done

if [ -z "$OP" ]; then
    echo "--op is required. Registered ops: ${OPS[*]}" >&2
    exit 2
fi

found=0
for o in "${OPS[@]}"; do
    if [ "$o" = "$OP" ]; then found=1; fi
done
if [ "$found" -eq 0 ]; then
    echo "Unknown --op $OP. Registered ops: ${OPS[*]}" >&2
    exit 2
fi

SPEC="$SCRIPT_DIR/arith_spec_${OP}.lean"
GEN_RS="$SCRIPT_DIR/generated.rs"
BIN="/tmp/arith_${OP}"
VECTORS_DIR="$SCRIPT_DIR/test_vectors/arith_${OP}"

echo "=== Integration Test: arith_spec_${OP} via trzk ==="

# 1. Build unconditionally (cheap when up-to-date). `lake build` resolves to
# defaultTargets (TRZK, Tests, trzk); we need the TRZK lib oleans on disk
# because the trzk runner re-elaborates a temp file via `lake env lean --run`.
(cd "$PROJECT_ROOT" && lake build)

# 2. Generate Rust from spec.
echo "Generating Rust from arith_spec_${OP}.lean..."
"$TRZK" "$SPEC" --name "arith_spec" --output "$GEN_RS"

# Arity per op. Future ops (sar) add rows here. The harness picks an
# arity-specific arm via `--cfg arity="N"`; pass --check-cfg so rustc doesn't
# warn about the custom cfg key.
# Note: `shr` arity is 1 because the spec reduces to `x0` after saturation.
case "$OP" in
    add0) ARITY=1 ;;
    mul) ARITY=2 ;;
    idiv1) ARITY=1 ;;
    shl) ARITY=2 ;;
    shr) ARITY=1 ;;
    *) echo "Internal error: no arity registered for op '$OP'" >&2; exit 2 ;;
esac

# 3. Compile harness (which #[path]s the generated file).
echo "Compiling..."
rustc -O --edition 2024 \
    --check-cfg 'cfg(arity, values("1", "2"))' \
    --cfg "arity=\"${ARITY}\"" \
    "$SCRIPT_DIR/harness.rs" -o "$BIN"

# 4. Verify.
RESULT=0
if [ "$FUZZ" -eq 1 ]; then
    if [ -n "$FUZZ_COUNT" ]; then
        python3 "$SCRIPT_DIR/generators/arith.py" --op "$OP" -n "$FUZZ_COUNT" \
            | python3 "$SCRIPT_DIR/verify_arith.py" --binary "$BIN" --arity "$ARITY" --fuzz \
            || RESULT=$?
    else
        python3 "$SCRIPT_DIR/generators/arith.py" --op "$OP" \
            | python3 "$SCRIPT_DIR/verify_arith.py" --binary "$BIN" --arity "$ARITY" --fuzz \
            || RESULT=$?
    fi
else
    cat "$VECTORS_DIR"/*.txt \
        | python3 "$SCRIPT_DIR/verify_arith.py" --binary "$BIN" --arity "$ARITY" \
        || RESULT=$?
fi

# 5. Cleanup.
rm -f "$GEN_RS" "$BIN"
rm -rf "$SCRIPT_DIR/artifacts"

if [ $RESULT -eq 0 ]; then
    echo "=== Integration test PASSED (op ${OP}) ==="
else
    echo "=== Integration test FAILED (op ${OP}) ==="
fi
exit $RESULT
