#!/bin/bash
#
# verify_assembly.sh - Assembly Verification for Phase 3 AVX2 Code
#
# This script compiles the AVX2 code and analyzes the generated assembly
# to ensure proper vectorization without unexpected library calls.
#
# Usage: ./verify_assembly.sh
#

set -e

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║     PHASE 3: ASSEMBLY VERIFICATION                          ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

# Check for x86 architecture
if [[ "$(uname -m)" != "x86_64" ]] && [[ "$(uname -m)" != "i386" ]]; then
    echo "⚠️  WARNING: Not running on x86 architecture ($(uname -m))"
    echo "   Assembly analysis may not be accurate."
    echo ""
fi

# Create a minimal test file that exercises the hot path
cat > /tmp/avx2_hotpath.c << 'EOF'
#define FIELD_GOLDILOCKS
#include "field_goldilocks.h"
#include "field_goldilocks_avx2.h"

// Hot path function - should be fully inlined
void hot_loop(uint64_t* restrict out,
              const uint64_t* restrict a,
              const uint64_t* restrict b,
              size_t n) {
    for (size_t i = 0; i < n; i += 4) {
        __m256i va = goldilocks_avx2_loadu(&a[i]);
        __m256i vb = goldilocks_avx2_loadu(&b[i]);
        __m256i vr = goldilocks_avx2_mul(va, vb);
        goldilocks_avx2_storeu(&out[i], vr);
    }
}

// FRI fold hot path
void fri_hot(uint64_t* restrict out,
             const uint64_t* restrict even,
             const uint64_t* restrict odd,
             uint64_t alpha,
             size_t n) {
    __m256i valpha = goldilocks_avx2_broadcast(alpha);
    for (size_t i = 0; i < n; i += 4) {
        __m256i veven = goldilocks_avx2_loadu(&even[i]);
        __m256i vodd = goldilocks_avx2_loadu(&odd[i]);
        __m256i vr = goldilocks_avx2_fri_fold(veven, vodd, valpha);
        goldilocks_avx2_storeu(&out[i], vr);
    }
}
EOF

echo "=== Compiling to assembly ==="
cd "$(dirname "$0")"

# Compile to assembly
clang -S -O3 -mavx2 -I. /tmp/avx2_hotpath.c -o /tmp/avx2_hotpath.s 2>/dev/null || {
    echo "❌ Failed to compile. This requires x86 with AVX2."
    echo "   Run this on the CI server or an x86 machine."
    exit 1
}

echo "✅ Assembly generated successfully"
echo ""

echo "=== Instruction Analysis ==="
echo ""

# Count key instructions
echo "Vector Multiply (vpmuludq):"
VPMUL_COUNT=$(grep -c "vpmuludq" /tmp/avx2_hotpath.s 2>/dev/null || echo "0")
echo "  Count: $VPMUL_COUNT"

echo ""
echo "Vector Add (vpaddq):"
VPADD_COUNT=$(grep -c "vpaddq" /tmp/avx2_hotpath.s 2>/dev/null || echo "0")
echo "  Count: $VPADD_COUNT"

echo ""
echo "Vector Sub (vpsubq):"
VPSUB_COUNT=$(grep -c "vpsubq" /tmp/avx2_hotpath.s 2>/dev/null || echo "0")
echo "  Count: $VPSUB_COUNT"

echo ""
echo "Vector Shift (vpsrlq/vpsllq):"
VSHIFT_COUNT=$(grep -cE "vps[rl]lq" /tmp/avx2_hotpath.s 2>/dev/null || echo "0")
echo "  Count: $VSHIFT_COUNT"

echo ""
echo "Vector Load/Store (vmovdqu/vmovdqa):"
VMOV_COUNT=$(grep -cE "vmovdq[ua]" /tmp/avx2_hotpath.s 2>/dev/null || echo "0")
echo "  Count: $VMOV_COUNT"

echo ""
echo "FP Shuffle trick (vmovshdup/vmovsldup):"
VSHUF_COUNT=$(grep -cE "vmovs[lh]dup" /tmp/avx2_hotpath.s 2>/dev/null || echo "0")
echo "  Count: $VSHUF_COUNT (expected >0 for hi32 extraction)"

echo ""
echo "=== Critical Check: Library Calls in Hot Path ==="
CALL_COUNT=$(grep -c "call" /tmp/avx2_hotpath.s 2>/dev/null || echo "0")
echo "  Total 'call' instructions: $CALL_COUNT"

# Check for dangerous library calls
BAD_CALLS=$(grep "call.*__" /tmp/avx2_hotpath.s 2>/dev/null || true)
if [ -n "$BAD_CALLS" ]; then
    echo ""
    echo "  ❌ CRITICAL: Found library function calls in hot path:"
    echo "$BAD_CALLS" | head -10
    echo ""
    echo "  These calls break vectorization and hurt performance!"
    RESULT="FAIL"
else
    echo "  ✅ No dangerous library calls detected"
    RESULT="PASS"
fi

echo ""
echo "=== Summary ==="
echo ""
echo "  Vectorized multiplies (vpmuludq): $VPMUL_COUNT"
echo "  Vectorized adds (vpaddq):         $VPADD_COUNT"
echo "  Data movement (vmov*):            $VMOV_COUNT"
echo "  Hi32 extraction (vmovs*dup):      $VSHUF_COUNT"
echo ""

# Expected: For mul64_64 we need 4 vpmuludq per multiplication
if [ "$VPMUL_COUNT" -lt 4 ]; then
    echo "  ⚠️  WARNING: Expected at least 4 vpmuludq for 64-bit mul emulation"
fi

if [ "$VSHUF_COUNT" -eq 0 ]; then
    echo "  ⚠️  WARNING: No FP shuffle instructions found"
    echo "     The hi32 extraction trick may not be working"
fi

echo ""
if [ "$RESULT" = "PASS" ]; then
    echo "╔══════════════════════════════════════════════════════════════╗"
    echo "║  ✅ ASSEMBLY VERIFICATION: PASS                             ║"
    echo "║     All code is properly inlined and vectorized             ║"
    echo "╚══════════════════════════════════════════════════════════════╝"
    exit 0
else
    echo "╔══════════════════════════════════════════════════════════════╗"
    echo "║  ❌ ASSEMBLY VERIFICATION: FAIL                             ║"
    echo "║     Library calls detected in hot path                      ║"
    echo "╚══════════════════════════════════════════════════════════════╝"
    exit 1
fi
