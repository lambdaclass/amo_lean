#!/usr/bin/env python3
"""v3.14.0 M.5: Feedback loop — compare cost model predictions vs benchmark measurements.

3 layers:
  Layer 1 (Predict): Extract cost predictions from planTotalCostWith (via trzk-gen report)
  Layer 2 (Measure): Run benchmark.py for each plan variant
  Layer 3 (Adjust):  Detect divergences, suggest adjustments (advisory)

Protocol (MANDATORY for new candidates):
  1. Add candidate to generateCandidates
  2. selectBestPlan predicts ranking
  3. This script measures ALL candidates
  4. Compare prediction vs measurement
  5. If divergence > 20%: diagnose, suggest adjustment
  6. ONLY then close the block as PASS

Usage:
  python3 Tests/benchmark/feedback_loop.py --field goldilocks --logn 14
  python3 Tests/benchmark/feedback_loop.py --field babybear --logn 14
"""

import argparse
import subprocess
import sys
import os
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from field_defs import get_field


# ══════════════════════════════════════════════════════════════════
# Layer 1: Predict — extract cost model predictions
# ══════════════════════════════════════════════════════════════════

def extract_predictions(field: str, logn: int, project_root: Path) -> dict:
    """Extract cost predictions by running trzk-gen and parsing the report.
    Returns: {plan_name: predicted_cost}
    """
    # Generate via trzk-gen which prints the Ultra pipeline report
    lean_code = f"""
import AmoLean.EGraph.Verified.Bitwise.UltraPipeline
import AmoLean.EGraph.Verified.Bitwise.NTTPlanSelection
open AmoLean.EGraph.Verified.Bitwise.UltraPipeline (goldilocksUltra babyBearUltra)
open AmoLean.EGraph.Verified.Bitwise.PlanSelection (planTotalCostWith generateCandidates mkTwoStepPlan selectBestPlan)
open AmoLean.EGraph.Verified.Bitwise.NTTPlan (NTTStage mkBoundAwarePlan)
open AmoLean.EGraph.Verified.Bitwise

def main : IO Unit := do
  let hw := arm_cortex_a76
  let p := {"18446744069414584321" if field == "goldilocks" else "2013265921"}
  let n := 2 ^ {logn}
  let candidates := generateCandidates p n hw
  IO.println "=== FEEDBACK LOOP: Cost Predictions ==="
  IO.println s!"Field: {field}, N=2^{logn}"
  IO.println s!"Candidates: {{candidates.size}}"
  let mut i := 0
  for c in candidates.toList do
    let cost := planTotalCostWith c hw
    let shiftStages := c.stages.foldl (fun n (s : NTTStage) => if s.useShift then n+1 else n) 0
    IO.println s!"  [{{i}}] cost={{cost}} stages={{c.stages.size}} shift={{shiftStages}}"
    i := i + 1
  let best := selectBestPlan p n hw
  let bestCost := planTotalCostWith best hw
  IO.println s!"Winner: cost={{bestCost}} stages={{best.stages.size}}"
"""
    lean_file = "/tmp/feedback_predict.lean"
    with open(lean_file, "w") as f:
        f.write(lean_code)

    r = subprocess.run(
        ["lake", "env", "lean", "--run", lean_file],
        capture_output=True, text=True, timeout=300,
        cwd=str(project_root)
    )
    if r.returncode != 0:
        print(f"[PREDICT] Lean failed: {r.stderr[:300]}")
        return {}

    print(r.stdout)
    # Parse predictions from output
    predictions = {}
    for line in r.stdout.split("\n"):
        line = line.strip()
        if line.startswith("[") and "cost=" in line:
            idx = line.split("]")[0].strip("[")
            cost = int(line.split("cost=")[1].split(" ")[0])
            predictions[f"candidate_{idx}"] = cost
        elif line.startswith("Winner:"):
            cost = int(line.split("cost=")[1].split(" ")[0])
            predictions["winner"] = cost

    return predictions


# ══════════════════════════════════════════════════════════════════
# Layer 2: Measure — benchmark the winning plan
# ══════════════════════════════════════════════════════════════════

def measure_winner(field: str, logn: int, project_root: Path) -> float:
    """Measure the actual NTT performance using benchmark.py.
    Returns: ns per element (or -1 on error)
    """
    bench_script = project_root / "Tests" / "benchmark" / "benchmark.py"
    if not bench_script.exists():
        print(f"[MEASURE] benchmark.py not found at {bench_script}")
        return -1

    # Use validation-only mode to get timing info
    r = subprocess.run(
        ["python3", str(bench_script),
         "--fields", field, "--sizes", str(logn),
         "--validation-only", "--pipeline", "ultra"],
        capture_output=True, text=True, timeout=600,
        cwd=str(project_root)
    )

    if r.returncode != 0:
        print(f"[MEASURE] Benchmark failed: {r.stderr[:300]}")
        return -1

    print(f"[MEASURE] Output:\n{r.stdout[:500]}")
    return 0  # Placeholder — actual ns parsing depends on benchmark.py output format


# ══════════════════════════════════════════════════════════════════
# Layer 3: Adjust — detect divergences, suggest fixes
# ══════════════════════════════════════════════════════════════════

def analyze_divergences(predictions: dict, measurement_ns: float):
    """Compare predictions vs measurement. Report divergences."""
    print("\n=== FEEDBACK LOOP: Divergence Analysis ===")
    if not predictions:
        print("  No predictions available (Lean failed)")
        return

    winner_cost = predictions.get("winner", 0)
    n_candidates = len([k for k in predictions if k.startswith("candidate_")])

    print(f"  Predicted winner cost: {winner_cost}")
    print(f"  Total candidates evaluated: {n_candidates}")

    if measurement_ns > 0:
        print(f"  Measured: {measurement_ns:.1f} ns/elem")
        # Check if ranking matches (would need all candidates measured)
        print("  Ranking comparison: requires all-candidate measurement (not yet implemented)")
    else:
        print("  Measurement: skipped or failed")

    # Cost model summary
    costs = sorted([(v, k) for k, v in predictions.items() if k.startswith("candidate_")])
    if costs:
        print(f"\n  Cost ranking (predicted):")
        for i, (cost, name) in enumerate(costs[:5]):
            marker = " <<<" if cost == winner_cost else ""
            print(f"    {i+1}. {name}: {cost}{marker}")
        if len(costs) > 5:
            print(f"    ... and {len(costs)-5} more")

    print("\n  Status: PREDICTIONS EXTRACTED. Full measurement comparison")
    print("  requires running benchmark.py with per-plan generation (future M.5 enhancement).")


# ══════════════════════════════════════════════════════════════════
# Main
# ══════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(description="v3.14.0 M.5: Feedback Loop")
    parser.add_argument("--field", default="goldilocks", help="Field name")
    parser.add_argument("--logn", type=int, default=14, help="log2(N)")
    parser.add_argument("--measure", action="store_true", help="Also run benchmarks (slow)")
    parser.add_argument("--project-root", default=None, help="Project root")
    args = parser.parse_args()

    if args.project_root:
        project_root = Path(args.project_root).resolve()
    else:
        project_root = Path(__file__).resolve().parent.parent.parent

    print(f"v3.14.0 Feedback Loop: {args.field} N=2^{args.logn}")
    print(f"Project: {project_root}")
    print()

    # Layer 1: Predict
    predictions = extract_predictions(args.field, args.logn, project_root)

    # Layer 2: Measure (optional, slow)
    measurement_ns = -1
    if args.measure:
        measurement_ns = measure_winner(args.field, args.logn, project_root)

    # Layer 3: Analyze
    analyze_divergences(predictions, measurement_ns)

    return 0


if __name__ == "__main__":
    sys.exit(main())
