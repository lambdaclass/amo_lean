#!/bin/bash
# AMO-Lean Benchmark: Extract C from Lean, compile, benchmark, report
#
# Usage: ./scripts/benchmark.sh [--quick]
#
# Requirements: cc (gcc or clang), Lean 4 toolchain (lake)

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
BUILD_DIR="$PROJECT_DIR/benchmark_output"
BENCH_SRC="$PROJECT_DIR/tests/interop/bench_butterfly.c"

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo -e "${BLUE}═══════════════════════════════════════════════════${NC}"
echo -e "${BLUE}  AMO-Lean Automated Benchmark${NC}"
echo -e "${BLUE}═══════════════════════════════════════════════════${NC}"
echo ""

# Step 1: Generate Rust modules from Lean
echo -e "${YELLOW}[1/4] Generating Rust modules from Lean...${NC}"
mkdir -p "$BUILD_DIR/rust"
cat > "$BUILD_DIR/gen_rust.lean" << 'LEANEOF'
import AmoLean.EGraph.Verified.Bitwise.MixedExprToRust
open AmoLean.EGraph.Verified.Bitwise.MixedExprToRust
def main : IO Unit := writeRustModules "benchmark_output/rust"
LEANEOF

cd "$PROJECT_DIR"
if lake env lean --run "$BUILD_DIR/gen_rust.lean" 2>/dev/null; then
    echo -e "${GREEN}  Rust modules generated successfully${NC}"
else
    echo "  Rust generation skipped (build the project first with 'lake build')"
fi

# Step 2: Generate C reductions from Lean
echo -e "${YELLOW}[2/4] Generating C reductions from Lean...${NC}"
cat > "$BUILD_DIR/gen_c.lean" << 'LEANEOF'
import AmoLean.EGraph.Verified.Bitwise.SynthesisToC
import AmoLean.EGraph.Verified.Bitwise.NTTBridge
open AmoLean.EGraph.Verified.Bitwise
open AmoLean.EGraph.Verified.Bitwise.NTTBridge

def main : IO Unit := do
  -- Emit reductions
  IO.println "// AMO-Lean generated reductions"
  IO.println "// Verified: solinasFold_mod_correct"
  IO.println ""
  IO.println "// Mersenne31"
  IO.println emitC_mersenne31
  IO.println ""
  IO.println "// BabyBear (ARM)"
  match emitC_babybear arm_cortex_a76 with
  | .ok code => IO.println code
  | .error _ => pure ()
  IO.println ""
  IO.println "// Goldilocks (FPGA)"
  match emitC_goldilocks fpga_dsp48e2 with
  | .ok code => IO.println code
  | .error _ => pure ()
  IO.println ""
  -- Emit butterfly
  IO.println "// BabyBear butterfly (direct Solinas fold)"
  let (sum, diff) := optimizeButterflyDirect babybear_prime
  IO.println sum
  IO.println diff
LEANEOF

if lake env lean --run "$BUILD_DIR/gen_c.lean" > "$BUILD_DIR/generated_reductions.c" 2>/dev/null; then
    echo -e "${GREEN}  C reductions written to benchmark_output/generated_reductions.c${NC}"
    head -5 "$BUILD_DIR/generated_reductions.c" | sed 's/^/    /'
else
    echo "  C generation skipped (build the project first)"
fi

# Step 3: Compile and run benchmark
echo ""
echo -e "${YELLOW}[3/4] Compiling and running butterfly benchmark...${NC}"

if [ ! -f "$BENCH_SRC" ]; then
    echo "  ERROR: bench_butterfly.c not found at $BENCH_SRC"
    exit 1
fi

CC="${CC:-cc}"
CFLAGS="-O2 -Wall"
BENCH_BIN="$BUILD_DIR/bench_butterfly"

$CC $CFLAGS -o "$BENCH_BIN" "$BENCH_SRC" 2>&1 | sed 's/^/    /'
echo -e "${GREEN}  Compiled with $CC $CFLAGS${NC}"
echo ""

# Run benchmark
"$BENCH_BIN" 2>&1 | tee "$BUILD_DIR/benchmark_results.txt"

# Step 4: Summary
echo ""
echo -e "${YELLOW}[4/4] Summary${NC}"
echo -e "${BLUE}═══════════════════════════════════════════════════${NC}"
echo ""
echo "  Output files:"
echo "    benchmark_output/generated_reductions.c  — C code from Lean"
echo "    benchmark_output/rust/                   — Rust modules for Plonky3"
echo "    benchmark_output/benchmark_results.txt   — Benchmark data"
echo ""
echo -e "  ${GREEN}To use the Rust modules:${NC}"
echo "    cd benchmark_output/rust && cargo test"
echo ""
echo -e "  ${GREEN}To integrate with Plonky3:${NC}"
echo "    Copy babybear.rs to your Plonky3 fork's field implementation"
echo "    Replace the reduce() function with BabyBear::reduce()"
echo ""

# Cleanup
rm -f "$BUILD_DIR/gen_rust.lean" "$BUILD_DIR/gen_c.lean"
