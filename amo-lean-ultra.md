# Plan: AMO-Lean Ultra — OptiSat v2 Integration + NTT Algorithmic Gap Closure

## Context

AMO-Lean's e-graph optimizes arithmetic (Solinas vs Montgomery vs Harvey) and generates NTT code **+15% faster** than Plonky3 on 31-bit fields, **+17-31%** on Goldilocks. Two gaps remain:

1. **Algorithmic gap**: `NTTFactorizationRules.lean` defines radix-2/4/split-radix strategies but they're **disconnected from codegen**. Codegen always emits radix-2. Connecting enables per-stage reduction, radix-4, and lazy reduction.

2. **Cost model gap**: `branchPenalty` is a hack. OptiSat v2's relational saturation can propagate output bounds (`x < k*p`) as first-class relations, eliminating the hack.

**Goal**: +20-30% vs Plonky3 (current +15% arithmetic + new +5-15% structure).

**Safety**: All 18-21 new files use the adaptor pattern. Zero modifications to existing 329 theorems. `MixedNodeOp` (52 importers) never touched.

## Architecture

```
Phase 22: Relational Bounds ──────┐    Phase 23: NTT Gap Closure
  7 files, ~2000 LOC              │      5-6 files, ~1900 LOC
  Track x < k*p as relations      │      NTTPlan + radix-4 + per-stage
  Replace branchPenalty            │      Connect NTTFactorizationRules
         ↓                        │                ↓
Phase 24: Colors + Ruler ─────────┤       (merges here)
  4-5 files, ~1500 LOC            │              ↓
  Hardware colors, auto-discovery  └──→ Phase 25: Pipeline + Benchmarks
                                          2-3 files, ~1000 LOC
```

Phases 22 and 23 are **independent** (parallelizable). Phase 24 depends on 22. Phase 25 depends on all.

## Phase 22: Relational Bound Propagation (~2000 LOC, 7 files)

Replace `branchPenalty` with formal bound tracking via OptiSat v2's relational saturation.

### DAG
```
N22.1 RelationTypes (FUND, 200 LOC, LOW)
  → N22.2 DirectedRelSpec (FUND, 300 LOC, MED)
    → N22.3 MultiRelEGraph (CRIT, 240 LOC, MED)
      → N22.4 MultiRelSaturateSpec (CRIT, 225 LOC, HIGH) ← de-risk gate
        → N22.5 Bound rules (CRIT, 350 LOC, HIGH)
        → N22.7 Backward compat (HOJA, 250 LOC, MED)
          → N22.6 Cross-relation NTT (PAR, 300 LOC, MED)
```

**N22.1**: Copy/adapt `SoundRelationRule`, `DirectedRelGraph`, `CrossRelationRule` from OptiSat `RelationTypes.lean` (216 LOC). Instantiate for `MixedNodeOp`.
- Source: `~/Documents/claudio/optisat/LambdaSat/RelationTypes.lean`
- Create: `AmoLean/EGraph/Verified/Bitwise/RelationTypes.lean`

**N22.3**: `MultiRelEGraph MixedNodeOp` — wrapper around existing `EGraph MixedNodeOp`, NOT a replacement.
- Source: `~/Documents/claudio/optisat/LambdaSat/MultiRelEGraph.lean` (120 LOC)
- Create: `AmoLean/EGraph/Verified/Bitwise/MultiRelMixed.lean`

**N22.4** ⚠ de-risk: Adapt `saturateColoredF_preserves_MRCV`. If >3 sessions, fall back to projecting MRCV to base CV only.

**N22.5**: Bound relation rules:
- `solinas_bound`: `solinasFold(x) < 2*p`
- `monty_bound`: `montyReduce(x) < p`
- `add_bound`: `a < k₁*p ∧ b < k₂*p → a+b < (k₁+k₂)*p`
- `harvey_1br_cond`: input < 2p → 1 branch
- `harvey_2br_cond`: input < 4p → 2 branches
- Create: `AmoLean/EGraph/Verified/Bitwise/BoundPropagation.lean`

**N22.7**: `v2_implies_v1_soundness` bridge to existing `pipeline_mixed_equivalent`.
- Source: `~/Documents/claudio/optisat/LambdaSat/MultiRelSoundness.lean:133-168`

## Phase 23: NTT Algorithmic-Arithmetic Gap (~1900 LOC, 5-6 files)

Connect `NTTFactorizationRules` to codegen. Radix-4 butterflies, DIT/DIF, per-stage reduction.

### DAG
```
N23.1 NTTPlan structure (FUND, 250 LOC, LOW)
N23.2 Radix-4 butterfly (FUND, 350 LOC, MED)
    ↘       ↙
N23.3 Plan selection (CRIT, 300 LOC, MED)
      ↓
N23.4 Codegen extension (CRIT, 350 LOC, HIGH)  N23.5 Per-stage reduction (PAR, 250 LOC)
      ↓
N23.6 Correctness bridge (HOJA, 275 LOC, HIGH) ← de-risk gate
```

**N23.1**: `NTTPlan` with per-stage granularity:
```lean
structure NTTStage where
  radix : Nat                 -- 2 or 4
  reduction : ReductionChoice -- solinasFold | harvey | monty | lazy
  direction : StageDirection  -- DIT | DIF
```
- Create: `AmoLean/EGraph/Verified/Bitwise/NTTPlan.lean`

**N23.2**: Radix-4 = 2× radix-2 composed. Prove `butterfly4_eq_compose_butterfly2`. Uses existing `butterflySum`/`butterflyDiff`.
- Create: `AmoLean/EGraph/Verified/Bitwise/Butterfly4Bridge.lean`

**N23.4**: Replace hardcoded `lowerNTT` with `lowerNTTFromPlan`. Backward compat: `generateNTT` calls it with default all-radix-2 plan.
- Modify: `UnifiedCodeGen.lean` (+200 LOC)
- Create: `AmoLean/EGraph/Verified/Bitwise/NTTPlanCodeGen.lean`

**N23.5**: Per-stage reduction scheduling: reduce when bound factor `k > 2` (Solinas) or `k > 4` (Harvey). Integrates with Phase 22 when available.

**N23.6** ⚠ de-risk: `nttPlan_semantic_preservation`. Factor through existing `ntt_generic_eq_spec`. If intractable, `native_decide` for BabyBear N=16 + documented sorry.

## Phase 24: Conditional Rules + Ruler (~1500 LOC, 4-5 files)

### DAG
```
N24.1 ColorTypes (FUND, 250 LOC, LOW) ← depends on N22.4
  → N24.2 ColoredSpec (CRIT, 300 LOC, HIGH)
    → N24.3 Hardware rules (PAR, 250 LOC)  N24.4 Ruler CVec (PAR, 300 LOC, MED)
      ↘                                    ↙
    N24.5 Ruler integration (HOJA, 250 LOC, HIGH) ← de-risk gate
```

**N24.1**: Hardware colors: `colorScalar(root) → colorSimd → colorNeon/colorAvx2`.
- Source: `~/Documents/claudio/optisat/LambdaSat/ColorTypes.lean` (268 LOC)

**N24.3**: Under `colorSimd`: NEON intrinsics. Under `colorScalar`: scalar ops. One e-graph, both targets.

**N24.4**: Ruler CVec for MixedNodeOp. Multi-mode: `.eq`, `.le`, `.dvd`, `.modN`.
- Source: `~/Documents/claudio/optisat/LambdaSat/Ruler/CVecEngine.lean` (208 LOC)

**N24.5** ⚠ de-risk: If SelfImprovement fails, manually write 5-10 key rules instead.

**Ruler discovery targets**: `x*(2^24-1) = (x<<24)-x`, fold fusion, second-fold bounds.

## Phase 25: Pipeline + Benchmarks (~1000 LOC, 2-3 files)

**N25.1**: `ultra_pipeline_soundness` — compose all phases. Bridge to `pipeline_mixed_equivalent`.
**N25.2**: Rust benchmarks for BabyBear/Goldilocks/KoalaBear with radix-4 + per-stage lazy.
**N25.3**: Compare vs Plonky3 `Radix2Bowers::dft_batch`.

### Targets
- BabyBear NTT: **+25-30%** vs Plonky3
- Goldilocks NTT: **+15-20%** vs Plonky3
- KoalaBear NTT: **+20-25%** vs Plonky3

## Totals

| | Phase 22 | Phase 23 | Phase 24 | Phase 25 | Total |
|---|---------|---------|---------|---------|-------|
| Files | 7 | 5-6 | 4-5 | 2-3 | 18-21 |
| LOC | ~2000 | ~1900 | ~1500 | ~1000 | ~6400 |
| Theorems | ~30 | ~20 | ~20 | ~10 | ~80 |
| Modified | 0 | 1 | 0 | 0 | 1 |
| Sorry | 0 | 0 | 0 | 0 | 0 |

## Risk Mitigation

| Risk | Mitigation |
|------|-----------|
| Type cascade (52 files) | Adaptor wraps, never modifies MixedNodeOp |
| MixedEMatchSoundness | Never touched. MRCV sits above e-match layer |
| Radix-4 verification | Reduce to 2× radix-2 (standard factorization) |
| Lazy reduction bounds | OptiSat relational saturation verifies formally |
| E-graph explosion | TieredSatConfig: eq every 1, rel every 3, cross every 5 |
| Ruler failure | De-risk: skip to manual rules |

## Critical files NOT to modify

- `MixedNodeOp.lean` (503 LOC) — 52 importers
- `MixedEMatchSoundness.lean` (1918 LOC) — most fragile
- `MixedSemanticSpec.lean` (175 LOC) — CV definition
- `PipelineSoundness.lean` (285 LOC) — master theorem

## Source files to copy/adapt from OptiSat

- `LambdaSat/RelationTypes.lean` → N22.1
- `LambdaSat/MultiRelEGraph.lean` → N22.3
- `LambdaSat/MultiRelSaturate.lean` → N22.4
- `LambdaSat/MultiRelSoundness.lean` → N22.7
- `LambdaSat/ColorTypes.lean` → N24.1
- `LambdaSat/Ruler/CVecEngine.lean` → N24.4
- `LambdaSat/Ruler/SelfImprovement.lean` → N24.5

## Verification

Each phase has a soundness theorem composing into `ultra_pipeline_soundness`:
1. Phase 22: `saturateColoredF_preserves_MRCV`
2. Phase 23: `nttPlan_semantic_preservation`
3. Phase 24: `soundColoredRule_preserves_CCV`
4. Phase 25: composition of above + `v2_implies_v1_soundness` bridge

`lake build` 0 errors after each node. `#print axioms` 0 custom axioms on master theorem.

## Gap Analysis: Two-Layer Optimization Connection (2026-03-27)

### The Problem

The original vision for AMO-Lean Ultra was two optimization layers that feed each other:

```
Level 1 (algorithmic): HOW to factorize NTT (radix-2/4, DIT/DIF, split-radix, Kronecker)
    ↕  feedback: Level 2 costs guide Level 1 factorization choices
Level 2 (arithmetic): HOW to implement each butterfly (Solinas/Montgomery/Harvey/lazy)
```

After Phases 22-23 were completed, an audit revealed that **Level 2 is fully built but Level 1 has no executor**:

- `NTTFactorizationRules.lean` defines 4 `MatRewriteRule`s over `MatENodeOp` — but nobody calls them
- `NTTPlanSelection.generateCandidates` hardcodes 5 candidates (all radix-2) — no exploration
- `Butterfly4Bridge.lean` (200 LOC, proven radix-4 cost savings) has zero consumers
- The two levels operate independently; there is no feedback loop

### What Works Today

| Component | Status | File |
|-----------|--------|------|
| Bound propagation through computation graph | COMPLETE | MultiRelMixed + BoundPropagation |
| Per-stage reduction selection (Solinas/Montgomery/Harvey/lazy) | COMPLETE | CrossRelNTT + NTTPlanSelection |
| Lazy reduction safety checking | COMPLETE | BoundPropagation.lazyReductionSafe |
| Colored e-graphs (SIMD vs scalar) | COMPLETE | HardwareColors |
| Ruler CVec matching (discover equivalences) | COMPLETE | RulerDiscovery |
| Radix-4 butterfly (proven cheaper) | COMPLETE but ORPHANED | Butterfly4Bridge |
| NTTPlan per-stage structure | COMPLETE | NTTPlan |
| Plan-driven codegen (radix-2 AND radix-4) | COMPLETE | NTTPlanCodeGen |

### What's Missing

1. **MatEGraph saturation loop**: `MatENodeOp` type exists (12 constructors), rules exist (4 factorization rules), but there's no e-graph structure, no rule application, no saturation loop.

2. **Cost oracle feedback**: Level 2 has `selectReductionForBound` + `reductionCost` + hardware cost models. Level 1 cannot query these. The feedback channel doesn't exist.

3. **MatEGraph → NTTPlan extraction**: No mechanism to convert a saturated algorithmic e-graph into a concrete `NTTPlan.Plan` with per-stage decisions.

4. **Correctness bridge**: `nttPlan_semantic_preservation` (plan preserves NTT semantics) depends on butterfly foldl lemmas in `StageSimulation.lean` — these are being proven but not yet complete.

### Resolution: Integrated into Fase 24 (ARCHITECTURE.md)

Rather than creating a separate Fase 25, the gap closure was integrated into Fase 24 (Discovery Engine) as two new nodes:

- **N24.11 MatEGraphStep** (FUND, ~300 LOC, Block B97): Saturation loop for MatRewriteRule. Reuses `threePhaseSaturateF` pattern from GuidedSaturation. Cost oracle queries Level 2 for arithmetic costs.
- **N24.12 MatPlanExtraction** (CRIT, ~200 LOC, Block B98): Extract optimal NTTPlan from saturated MatEGraph. Includes `refinePlanWithBounds` (post-extraction bound optimization) and `nttPlan_semantic_preservation` theorem.

Rationale: Fase 24 is "Discovery Engine" — algorithmic exploration IS discovery. GuidedSaturation (N24.5) is the natural foundation. The two new nodes insert between N24.5 and N24.9 (DiscoveryPipeline) in the topological order.

### Quick Win (independent, any time)

Extend `generateCandidates` with radix-4 candidates (~100 LOC). This activates `Butterfly4Bridge` and captures ~80% of radix-4 value via enumeration rather than exploration. Does NOT replace N24.11/N24.12 but provides immediate benefit.
