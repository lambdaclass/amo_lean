# Truth Ultra: Verified SPIRAL — Joint Algorithmic-Arithmetic NTT Optimization

## Vision

Transform AMO-Lean from a verified arithmetic optimizer into a **verified SPIRAL**: a system that jointly optimizes **what algorithm to use** (radix-2, radix-4, split-radix, Bowers) and **how to implement each operation** (Solinas fold, Montgomery REDC, Harvey lazy reduction) — all within a single verified framework.

No existing system does this. SPIRAL optimizes both levels but has no formal verification. Fiat-Crypto verifies arithmetic but doesn't choose algorithms. Plonky3 chooses algorithms but verifies nothing. HELIX (Coq) verifies SPIRAL's output but uses SPIRAL as an untrusted oracle. Truth Ultra builds the optimization engine *inside* the proof assistant, making the oracle unnecessary.

**Target**: +25-35% vs Plonky3 on NTT (currently +15-20%), with every decision formally verified.

---

## Architectural Principle: Five Levels of Responsibility

The core insight from our analysis: different optimization concerns live at different levels. Mixing them (e.g., putting cache costs in per-node cost functions) creates hacks. Separating them creates a clean, extensible architecture.

```
┌─────────────────────────────────────────────────────────────┐
│ LEVEL 1: ALGORITHMIC E-GRAPH (MatENodeOp)                   │
│  What: Explore factorizations as equivalence classes         │
│  How:  MatExpr e-graph with breakdown rules                  │
│  Decides: WHICH factorization (radix-2/4, DIT/DIF, Bowers)  │
│  Also: Cache-aware plan selection (access pattern → cost)    │
│  Granularity: per-NTT                                        │
│  NEW in this plan (Phase 24)                                 │
└──────────────────────┬──────────────────────────────────────┘
                       │ queries cost per butterfly type
                       ↓
┌─────────────────────────────────────────────────────────────┐
│ LEVEL 2: ARITHMETIC E-GRAPH (MixedNodeOp, relational)       │
│  What: Discover equivalent implementations                   │
│  How:  Equality saturation + relational saturation           │
│  Knows: Solinas ≡ Montgomery ≡ Harvey (mod p)                │
│  Knows: solinasFold(x) < 2p (bounds as relations)           │
│  Knows: under color "SIMD", prefer Montgomery               │
│  Granularity: per-butterfly / per-operation                  │
│  ENHANCED in this plan (Phase 22, 25)                        │
└──────────────────────┬──────────────────────────────────────┘
                       │ saturated e-graph with bounds
                       ↓
┌─────────────────────────────────────────────────────────────┐
│ LEVEL 3: COST FUNCTION (per-node, hardware-parametric)      │
│  What: Assign concrete cost to each node                     │
│  How:  HardwareCost struct with per-op latencies             │
│  Covers: ALU latency, branch penalty (informed by bounds),   │
│          SIMD widening, register spill, energy               │
│  Does NOT cover: cache, ILP (those live elsewhere)           │
│  Granularity: per-node                                       │
│  ENRICHED in this plan (Phase 26)                            │
└──────────────────────┬──────────────────────────────────────┘
                       │ costs assigned to each e-node
                       ↓
┌─────────────────────────────────────────────────────────────┐
│ LEVEL 4: EXTRACTION (global optimization)                   │
│  What: Choose which equivalent to pick from each e-class     │
│  How:  Greedy (fast) or ILP (optimal) or DP (treewidth)      │
│  Can incorporate: critical path depth (ILP), register        │
│                   pressure (per-subtree penalty)             │
│  Granularity: per-e-class                                    │
│  ENHANCED in this plan (Phase 26)                            │
└──────────────────────┬──────────────────────────────────────┘
                       │ extracted MixedExpr
                       ↓
┌─────────────────────────────────────────────────────────────┐
│ LEVEL 5: SCHEDULING (post-extraction)                       │
│  What: Order instructions for the target                     │
│  How:  List scheduling with latency model                    │
│  Covers: ILP maximization, register allocation               │
│  Granularity: per-instruction                                │
│  ENHANCED in this plan (Phase 26)                            │
└─────────────────────────────────────────────────────────────┘
```

**Why this separation matters**: Each level has a well-defined interface. The algorithmic e-graph doesn't know about Solinas folds. The arithmetic e-graph doesn't know about cache lines. The cost function doesn't know about instruction ordering. Changes at one level don't cascade to others.

---

## Inventory: What We Have vs What We Build

### Existing in AMO-Lean (0 sorry, production-ready)

| Component | Files | LOC | Status |
|-----------|-------|-----|--------|
| MixedNodeOp (21 ops, NodeOps+Semantics) | 1 | 503 | ✓ verified |
| E-graph core (saturation, matching, extraction) | 6 | 2,970 | ✓ verified |
| MixedEMatchSoundness (full chain) | 1 | 1,918 | ✓ verified |
| Cost models (HardwareCost × 8 targets) | 2 | 652 | ✓ verified |
| Codegen (C/Rust/SIMD backends) | 7 | 3,339 | ✓ verified |
| NTT bridges + butterfly rules | 5 | 1,337 | ✓ verified |
| Pipeline (pipeline_mixed_equivalent) | 4 | 1,090 | ✓ verified |
| Rule sets + saturation strategies | 8 | 2,061 | ✓ verified |
| Discovery pipeline | 10 | 2,226 | ✓ operational |
| MatExpr AST + Perm theory | 2 | 1,354 | ✓ verified |
| MatENodeOp (structure only, no typeclass) | 1 | ~400 | ⚠ partial |
| Sigma IR + bridges | 7 | 2,457 | ✓ operational |
| **TOTAL existing** | **54+** | **~20,307** | |

### Available in OptiSat v2 (copy/adapt, NOT import)

| Component | Source files | LOC | Genericity |
|-----------|-------------|-----|------------|
| ColorHierarchy + SmallUF | ColorTypes.lean | 268 | ✓ fully generic |
| ColoredLayer + merge | ColoredMerge.lean | 295 | ✓ fully generic |
| Colored specification (CCV) | ColoredSpec.lean | 350 | ✓ fully generic |
| ColoredEMatch | ColoredEMatch.lean | 141 | ✓ fully generic |
| ColoredRebuild | ColoredRebuild.lean | 190 | ✓ fully generic |
| SoundRelationRule + DirectedRelGraph | RelationTypes.lean | 216 | ✓ fully generic |
| DirectedRelSpec | DirectedRelSpec.lean | ~400 | ✓ fully generic |
| CrossRelationRule + composition | RelationTypes.lean | (included) | ✓ fully generic |
| MultiRelEGraph wrapper | MultiRelEGraph.lean | 120 | ✓ fully generic |
| TieredSatConfig + saturateColoredF | MultiRelSaturate.lean | 250 | ✓ fully generic |
| full_pipeline_v2_soundness | MultiRelSoundness.lean | 180 | ✓ fully generic |
| v2_implies_v1_soundness | MultiRelSoundness.lean | (included) | ✓ fully generic |
| CVecEngine | Ruler/CVecEngine.lean | 208 | ⚠ Nat-specific |
| SelfImprovement loop | Ruler/SelfImprovement.lean | 200 | ✓ generic |
| GrowthPrediction + SizeChange | (multiple) | 425 | ✓ generic |
| **TOTAL copyable** | **~15 files** | **~3,243** | |

**Key fact**: OptiSat v2 is fully parameterized by `Op`. Since `MixedNodeOp` already implements `NodeOps` and `NodeSemantics`, instantiation is mechanical — provide the instances, the theorems follow.

### Must Build New (~8,800 LOC estimated)

| Component | Est. LOC | Phase | Risk |
|-----------|----------|-------|------|
| BoundPropagation rules (field-specific) | 350 | 22 | LOW |
| DirectedRelSpec adaptation | 300 | 22 | MED |
| Cross-relation NTT rules | 300 | 22 | MED |
| Backward compat bridge | 250 | 22 | LOW |
| NTTPlan structure | 250 | 23 | LOW |
| Butterfly4Bridge (radix-4 = 2× radix-2) | 350 | 23 | MED |
| NTTPlanCodeGen (plan-driven codegen) | 350 | 23 | MED |
| Per-stage reduction scheduling | 250 | 23 | MED |
| Cache-aware plan selection | 350 | 23 | MED |
| Correctness bridge (plan → NTT) | 300 | 23 | HIGH |
| MatENodeOp → NodeOps instance | 200 | 24 | LOW |
| MatENodeOp abstract semantics | 400 | 24 | HIGH |
| Matrix breakdown rules (SoundRewriteRule) | 600 | 24 | HIGH |
| Cross-e-graph cost protocol | 500 | 24 | HIGH |
| Composition theorems (butterfly → NTT) | 800 | 24 | HIGH |
| MatExpr extraction | 400 | 24 | MED |
| NTTPlan integration | 300 | 24 | MED |
| HardwareCost enrichment (branch/energy) | 150 | 26 | LOW |
| NTTPlan cache model | 400 | 26 | MED |
| ILP-aware extraction adapter | 500 | 26 | HIGH |
| Post-extraction scheduler | 500 | 26 | MED |
| Ultra pipeline soundness | 400 | 27 | MED |
| Benchmarks (Rust, comparison) | 800 | 27 | LOW |
| **TOTAL new** | **~8,750** | | |

### Summary

| Category | LOC | Files |
|----------|-----|-------|
| Existing (AMO-Lean) | ~20,307 | 54+ |
| Copy/adapt (OptiSat v2) | ~3,243 | ~15 |
| Build new | ~8,750 | ~25-30 |
| **TOTAL after completion** | **~32,300** | **~95-100** |

---

## Phase Architecture

```
Phase 22: Relational Bounds ──────────┐
  7 files, ~2,200 LOC                 │
  Bounds as relations in e-graph      │
  Replace branchPenalty               │    Phase 23: NTT Gap Closure
  OptiSat v2 MultiRelEGraph           │      6 files, ~2,050 LOC
         │                            │      NTTPlan + radix-4 + per-stage
         │                            │      Cache-aware plan selection
         ↓                            │               │
Phase 25: Colors + Ruler ─────────────┤               │
  5 files, ~1,500 LOC                 │               │
  Hardware colors, auto-discovery     │               │
         │                            ↓               ↓
         └───────────────────→ Phase 24: Joint Optimization ←────┘
                                 8 files, ~3,200 LOC
                                 MatExpr e-graph (verified SPIRAL)
                                 Cross-e-graph protocol
                                 Composition theorems
                                        │
                                        ↓
                               Phase 26: Cost Architecture
                                 5 files, ~1,550 LOC
                                 Multi-level cost model
                                 ILP extraction, scheduling
                                        │
                                        ↓
                               Phase 27: Pipeline + Benchmarks
                                 3 files, ~1,200 LOC
                                 ultra_pipeline_soundness
                                 +25-35% vs Plonky3
```

**Parallelism**: Phases 22 and 23 are fully independent. Phase 25 depends on 22. Phase 24 depends on 22+23. Phase 26 depends on 24. Phase 27 depends on all.

---

## Phase 22: Relational Bound Propagation (~2,200 LOC, 7 files)

### Motivation

Today, `branchPenalty` in `CostModelDef.lean` is a magic number. It approximates the cost of conditional branches in Harvey reduction without knowing whether the input is bounded. With relational saturation from OptiSat v2, the e-graph would *know* that `solinasFold(x) < 2p` and propagate this bound through additions and multiplications. The cost function then consults the bound to determine the actual branch count — no hack needed.

This is a pure e-graph enhancement. The cost function doesn't change; what changes is the *information* available to it.

### What SPIRAL does differently

SPIRAL doesn't track bounds formally — it generates code, runs it, and measures. If an overflow occurs, the code is wrong. Truth Ultra makes overflow analysis a first-class verified property.

### DAG

```
N22.1 RelationTypes (FUND, 250 LOC, LOW)          ← copy/adapt from OptiSat
  → N22.2 DirectedRelSpec (FUND, 350 LOC, MED)    ← copy/adapt + new rules
    → N22.3 MultiRelMixed (CRIT, 280 LOC, MED)    ← copy/adapt MultiRelEGraph
      → N22.4 TieredSaturation (CRIT, 250 LOC, HIGH) ← de-risk gate
        → N22.5 BoundPropagation rules (CRIT, 350 LOC, MED)
          → N22.7 Backward compat bridge (HOJA, 250 LOC, MED)
            → N22.6 Cross-relation NTT (PAR, 300 LOC, MED)
```

### Node Details

**N22.1 — RelationTypes** (FUNDACIONAL, 250 LOC, LOW risk)

Copy/adapt from `~/Documents/claudio/optisat/LambdaSat/RelationTypes.lean` (216 LOC). Instantiate for `MixedNodeOp`:

```lean
-- The key relation for NTT: "x is bounded by k multiples of p"
def BoundedByKP (p : Nat) : Nat → Nat → Prop := fun x k => x < k * p

-- Sound relation rules for field reductions:
def solinas_bound_rule (p : Nat) : SoundRelationRule MixedNodeOp MixedExpr Nat (BoundedByKP p)
-- States: solinasFold(x) < 2 * p

def monty_bound_rule (p : Nat) : SoundRelationRule MixedNodeOp MixedExpr Nat (BoundedByKP p)
-- States: montyReduce(x) < p (i.e., k = 1)
```

Create: `AmoLean/EGraph/Verified/Bitwise/RelationTypes.lean`

**N22.3 — MultiRelMixed** (CRÍTICO, 280 LOC, MED risk)

Wrapper around existing `EGraph MixedNodeOp`, NOT a replacement. Adds relation DAGs alongside the base equality graph.

Copy from `~/Documents/claudio/optisat/LambdaSat/MultiRelEGraph.lean` (120 LOC) + adapt.

```lean
-- The enhanced e-graph with bound tracking
structure MultiRelMixed where
  baseGraph : EGraph MixedNodeOp          -- existing, untouched
  coloredLayer : ColoredLayer MixedNodeOp -- from Phase 25 (or stub)
  boundDag : DirectedRelGraph             -- bound relation: x < k*p
  assumptions : ColorAssumption Nat       -- color assumptions
```

Create: `AmoLean/EGraph/Verified/Bitwise/MultiRelMixed.lean`

**N22.4 — TieredSaturation** ⚠ de-risk gate (CRÍTICO, 250 LOC, HIGH risk)

Adapt `saturateColoredF` from OptiSat. The risk is ensuring `MRCV` (Multi-Relation Consistent Valuation) is preserved through saturation with `MixedNodeOp` rules.

**De-risk strategy**: If full MRCV preservation proof takes >3 sessions, fall back to projecting MRCV to base CV only (relation tracking becomes advisory, not verified). This still eliminates `branchPenalty` — the bounds inform the cost function even without formal MRCV.

**N22.5 — BoundPropagation** (CRÍTICO, 350 LOC, MED risk)

The domain-specific bound rules:

```lean
-- Solinas fold produces output < 2p
solinas_bound : ∀ x p, x < 2^64 → solinasFold x p < 2 * p

-- Montgomery produces output < p
monty_bound : ∀ x p, montyReduce x p < p

-- Addition propagates bounds
add_bound : ∀ a b p k₁ k₂, a < k₁*p → b < k₂*p → a + b < (k₁+k₂)*p

-- Harvey 1-branch condition: input must be < 2p
harvey_1br_cond : ∀ x p, x < 2*p → harveyReduce x p = if x ≥ p then x - p else x

-- Harvey 2-branch condition: input must be < 4p
harvey_2br_cond : ∀ x p, x < 4*p → harveyReduce x p needs at most 2 comparisons
```

Create: `AmoLean/EGraph/Verified/Bitwise/BoundPropagation.lean`

**N22.7 — Backward compatibility bridge** (HOJA, 250 LOC, MED risk)

Theorem proving that `v2_implies_v1_soundness` holds for our instantiation: when no relations are active, the enhanced pipeline reduces to the existing `pipeline_mixed_equivalent`.

Source: `~/Documents/claudio/optisat/LambdaSat/MultiRelSoundness.lean:133-168`

### Safety

- **Zero modifications** to existing files (except adding imports in root aggregator)
- `MixedEMatchSoundness.lean` (1,918 LOC) is NEVER touched
- `MixedNodeOp.lean` (52 importers) is NEVER touched
- All new structures are wrappers/adaptors

---

## Phase 23: NTT Algorithmic-Arithmetic Gap Closure (~2,050 LOC, 6 files)

### Motivation

`NTTFactorizationRules.lean` defines 5 factorization strategies. `UnifiedCodeGen.lean` always emits radix-2 DIT. The gap means the system can't exploit radix-4 (3.4x fewer total cycles for BabyBear N=1024) or per-stage lazy reduction.

This phase builds the bridge: a `NTTPlan` structure that carries per-stage decisions from the algorithmic level down to codegen.

### What SPIRAL does

SPIRAL's Σ-SPL level is exactly this: the `ISum` construct represents explicit loops with gather/scatter patterns derived from the chosen factorization. Our `SigmaExpr` in `Sigma/Basic.lean` already mirrors this. What's missing is making the factorization choice *dynamic* (driven by cost) instead of hardcoded.

### DAG

```
N23.1 NTTPlan structure (FUND, 250 LOC, LOW)
N23.2 Radix-4 butterfly (FUND, 350 LOC, MED)
    ↘       ↙
N23.3 Plan selection + cache model (CRIT, 350 LOC, MED)
      ↓
N23.4 Codegen extension (CRIT, 350 LOC, MED)   N23.5 Per-stage reduction (PAR, 250 LOC)
      ↓
N23.6 Correctness bridge (HOJA, 300 LOC, HIGH) ← de-risk gate
```

### Node Details

**N23.1 — NTTPlan** (FUNDACIONAL, 250 LOC, LOW risk)

```lean
inductive RadixChoice where | r2 | r4

inductive ReductionChoice where
  | solinasFold | harvey | montgomery | lazy (maxK : Nat)

inductive StageDirection where | DIT | DIF

structure NTTStage where
  radix : RadixChoice           -- 2 or 4
  reduction : ReductionChoice   -- which reduction after this stage
  direction : StageDirection    -- DIT or DIF

structure NTTPlan where
  stages : Array NTTStage
  field : Nat                   -- prime p
  size : Nat                    -- N (must be power of 2)
  ordering : NTTOrdering        -- standard, Bowers, or custom

inductive NTTOrdering where
  | standard    -- bit-reversal input, natural output
  | bowers      -- natural input, natural output (more memory passes)
  | custom (inputPerm outputPerm : Perm)
```

This is Level 1's output format — it tells Level 2 what to optimize per-stage.

Create: `AmoLean/EGraph/Verified/Bitwise/NTTPlan.lean`

**N23.2 — Radix-4 butterfly** (FUNDACIONAL, 350 LOC, MED risk)

Radix-4 butterfly = composition of two radix-2 butterflies. Prove:

```lean
theorem butterfly4_eq_compose_butterfly2 (a b c d w1 w2 w3 : Nat) (p : Nat) :
  butterfly4 a b c d w1 w2 w3 p =
    let (s1, d1) := butterfly2 a c w2 p
    let (s2, d2) := butterfly2 b d w3 p
    let (r1, r3) := butterfly2 s1 s2 w1 p
    let (r2, r4) := butterfly2 d1 d2 (w1 * twiddle_adjust) p
    (r1, r2, r3, r4)
```

Uses existing `butterflySum`/`butterflyDiff` from `NTTBridge.lean`.

Create: `AmoLean/EGraph/Verified/Bitwise/Butterfly4Bridge.lean`

**N23.3 — Plan selection + cache model** (CRÍTICO, 350 LOC, MED risk)

This is where Level 1 concerns (cache, access pattern) live — NOT in the per-node cost function.

```lean
structure CacheConfig where
  l1Size : Nat := 32768      -- 32KB L1 data cache
  lineSize : Nat := 64       -- 64-byte cache lines
  elementSize : Nat := 4     -- 4 bytes per u32 element

-- Cache cost is a property of the PLAN, not individual operations
def planCacheCost (plan : NTTPlan) (cache : CacheConfig) : Nat :=
  plan.stages.foldl (fun acc stage =>
    let blockSize := plan.size / (2 ^ stageIndex)
    let elementsPerBlock := blockSize * cache.elementSize
    let missRate := if elementsPerBlock ≤ cache.l1Size then 0 else
                    (elementsPerBlock - cache.l1Size) / cache.lineSize
    acc + missRate * cacheMissPenalty
  ) 0

-- Plan selection: total cost = Σ arithmetic costs + cache cost
def selectPlan (plans : List NTTPlan) (hw : HardwareCost)
    (cache : CacheConfig) (arithmeticCostFn : NTTStage → Nat) : NTTPlan :=
  plans.minBy (fun plan =>
    plan.stages.foldl (fun acc s => acc + arithmeticCostFn s) 0
    + planCacheCost plan cache)
```

Create: `AmoLean/EGraph/Verified/Bitwise/NTTPlanSelection.lean`

**N23.4 — Codegen extension** (CRÍTICO, 350 LOC, MED risk)

Replace hardcoded `lowerNTT` with `lowerNTTFromPlan`:

```lean
def lowerNTTFromPlan (plan : NTTPlan) (hw : HardwareCost) : Stmt :=
  plan.stages.foldl (fun acc stage =>
    let butterflyFn := match stage.radix with
      | .r2 => emitButterfly2 stage.reduction hw
      | .r4 => emitButterfly4 stage.reduction hw
    let loop := emitStageLoop stage butterflyFn
    Stmt.seq acc loop
  ) Stmt.skip
```

Backward compat: `generateNTT` calls `lowerNTTFromPlan` with a default all-radix-2 plan.

Modify: `UnifiedCodeGen.lean` (+200 LOC)
Create: `AmoLean/EGraph/Verified/Bitwise/NTTPlanCodeGen.lean`

**N23.6 — Correctness bridge** ⚠ de-risk gate (HOJA, 300 LOC, HIGH risk)

```lean
theorem nttPlan_semantic_preservation (plan : NTTPlan) (input : Array (ZMod p)) :
  evalNTTPlan plan input = ntt_spec p input
```

Factor through existing `ntt_generic_eq_spec` from Matrix level.

**De-risk**: If the general theorem is intractable, prove for specific cases:
1. `native_decide` for BabyBear N=16 (base case)
2. Compositional: if each stage is correct, the whole NTT is correct (induction on stages)

---

## Phase 24: Joint Optimization — Verified SPIRAL (~3,200 LOC, 8 files)

### Motivation

This is the heart of Truth Ultra and what makes it unique. Today, algorithmic choices (which factorization) and arithmetic choices (which reduction) are made independently. Phase 24 creates a protocol where the **algorithmic e-graph asks the arithmetic e-graph for costs**, enabling joint optimization.

### What SPIRAL does

SPIRAL's DP search builds rule trees bottom-up: for each subproblem (e.g., DFT of size 64), it tries all applicable breakdown rules, generates code for each, measures performance, and keeps the best. The "measurement" step is where SPIRAL consults the implementation level.

We replace measurement with **verified cost extraction**: the arithmetic e-graph computes the cost of each butterfly configuration, and the algorithmic e-graph uses these costs to select the optimal factorization.

### Architecture

```
MatExpr E-Graph (Level 1)
┌──────────────────────────────────┐
│ DFT_1024                          │
│   ≡ CT(32,32)  [Cooley-Tukey]    │
│   ≡ CT(4,256)  [Radix-4 outer]   │
│   ≡ Bowers(1024) [Bowers order]  │
│                                   │
│ Cost of CT(32,32):                │
│   query arithmetic e-graph for    │──→ Arithmetic E-Graph (Level 2)
│   cost(radix2_butterfly,          │    ┌─────────────────────────┐
│         BabyBear, ARM_NEON)       │    │ butterfly2(a,w,b,p)     │
│   × 5120 butterflies              │    │   ≡ solinas_version     │
│   + planCacheCost(CT_32_32)       │    │   ≡ montgomery_version  │
│                                   │    │   ≡ harvey_version      │
│ Cost of CT(4,256):                │    │                         │
│   query for cost(radix4_bf, ...)  │    │ Extract cheapest for    │
│   × 1280 butterflies              │    │ target hw → cost = 8    │
│   + planCacheCost(CT_4_256)       │    └─────────────────────────┘
│                                   │
│ Extract: CT(4,256) wins (17920 < 40960)
└──────────────────────────────────┘
```

### DAG

```
N24.1 MatENodeOp → NodeOps (FUND, 200 LOC, LOW)
  → N24.2 Abstract MatSemantics (FUND, 400 LOC, HIGH) ← de-risk gate
    → N24.3 Breakdown rules as SoundRewriteRule (CRIT, 600 LOC, HIGH)
      → N24.4 Cross-e-graph cost protocol (CRIT, 500 LOC, HIGH) ← de-risk gate
        → N24.5 Composition theorems (CRIT, 800 LOC, HIGH)
N24.6 MatExpr extraction (PAR, 400 LOC, MED)
N24.7 NTTPlan integration (HOJA, 300 LOC, MED)
```

### Node Details

**N24.1 — MatENodeOp → NodeOps** (FUNDACIONAL, 200 LOC, LOW risk)

The infrastructure already exists in `Vector.lean`. `MatENodeOp` has `children` and `mapChildren` defined but not bound to the typeclass. This is mechanical:

```lean
instance : NodeOps MatENodeOp where
  children := MatENode.children
  mapChildren := MatENode.mapChildren
  replaceChildren := MatENode.replaceChildren
  localCost := MatENode.localCost
  -- Laws: case analysis on MatENodeOp constructors
```

Create: `AmoLean/EGraph/Verified/Matrix/MatNodeOpsInstance.lean`

**N24.2 — Abstract MatSemantics** ⚠ de-risk gate (FUNDACIONAL, 400 LOC, HIGH risk)

The key design decision. Two options:

**Option A (Primary): Semantic labels, not matrices**

Don't evaluate MatExpr to actual matrices (which would require Mathlib's Matrix type over ZMod p). Instead, evaluate to a *semantic label* that identifies the transform:

```lean
-- A transform is identified by its input→output behavior on canonical inputs
structure TransformLabel where
  size : Nat × Nat           -- (input_dim, output_dim)
  id : Nat                    -- unique identifier

instance : NodeSemantics MatENodeOp TransformEnv TransformLabel where
  evalOp op env v := match op with
    | .dft n => ⟨(n, n), dft_id n⟩
    | .ntt n p => ⟨(n, n), ntt_id n p⟩
    | .kron a b m₁ n₁ m₂ n₂ => ⟨(m₁*m₂, n₁*n₂), kron_id (v a).id (v b).id⟩
    | .compose a b m k n => ⟨(m, n), compose_id (v a).id (v b).id⟩
    | ...
```

Breakdown rules then prove: `dft_label(n) = ct_label(r, s)` for all valid factorizations.

**Option B (Stretch goal): Concrete matrix semantics**

```lean
instance : NodeSemantics MatENodeOp (ZMod p) (Matrix (Fin n) (Fin n) (ZMod p)) where
  evalOp op env v := match op with
    | .dft n => dft_matrix n p  -- requires Mathlib
    | .kron a b ... => (v a) ⊗ₖ (v b)
    | ...
```

This gives the strongest guarantee but couples us to Mathlib's matrix library.

**De-risk**: Start with Option A. If the composition theorems (N24.5) are easier with concrete matrices, switch to Option B for the composition layer only.

**N24.3 — Breakdown rules** (CRÍTICO, 600 LOC, HIGH risk)

These are SPIRAL's core contribution, formalized as `SoundRewriteRule MatENodeOp`:

```lean
-- Cooley-Tukey: DFT(r*s) = (DFT(r) ⊗ I(s)) · T(rs,s) · (I(r) ⊗ DFT(s)) · L(rs,r)
def cooleyTukeyRule (r s : Nat) : SoundRewriteRule MatENodeOp where
  lhs := Pattern.node (.dft (r * s)) []
  rhs := Pattern.node (.compose ...) [
    Pattern.node (.kron ...) [Pattern.node (.dft r) [], Pattern.node (.identity s) []],
    Pattern.node (.twiddle (r*s) s) [],
    Pattern.node (.kron ...) [Pattern.node (.identity r) [], Pattern.node (.dft s) []],
    Pattern.node (.perm (.stride (r*s) r)) []
  ]
  soundness := cooleyTukey_correct r s  -- proved via Matrix/Perm theorems

-- Other breakdown rules:
-- goodThomasRule (r s : Nat) (h : Nat.Coprime r s) -- no twiddle factors
-- raderRule (p : Nat) (hp : Nat.Prime p)           -- prime-size via convolution
-- splitRadixRule (n : Nat) (h : 4 ∣ n)             -- hybrid 2+4
-- baseCase2 : SoundRewriteRule MatENodeOp           -- DFT(2) = F(2) butterfly
```

The existing `tensor_compose_pointwise` theorem in `Perm.lean` (198 LOC proof) is the mathematical backbone for Cooley-Tukey correctness.

Create: `AmoLean/EGraph/Verified/Matrix/BreakdownRules.lean`

**N24.4 — Cross-e-graph cost protocol** ⚠ de-risk gate (CRÍTICO, 500 LOC, HIGH risk)

The novel contribution. The protocol:

```lean
-- Query: "what does it cost to implement this butterfly on this hardware?"
structure ArithmeticCostQuery where
  butterflyType : ButterflyType     -- radix2_CT, radix4, etc.
  field : Nat                       -- prime p
  hw : HardwareCost                 -- target hardware
  boundsContext : BoundContext       -- what bounds are known from prior stages

-- Response: cost + chosen implementation
structure ArithmeticCostResponse where
  cycleCost : Nat                   -- total cycles for one butterfly
  chosenReduction : ReductionChoice -- what the arithmetic e-graph selected
  outputBound : Nat                 -- bound factor k for output (x < k*p)

-- The cross-e-graph function:
def queryArithmeticCost (arithmeticEGraph : EGraph MixedNodeOp)
    (query : ArithmeticCostQuery) : ArithmeticCostResponse :=
  -- 1. Build butterfly MixedExpr for the query
  let butterfly := buildButterfly query.butterflyType query.field
  -- 2. Insert into arithmetic e-graph
  let (rootId, g) := insertExpr arithmeticEGraph butterfly
  -- 3. Saturate with all rules (including bound rules from Phase 22)
  let g_sat := saturateMixedF g allRules satFuel
  -- 4. Extract cheapest implementation
  let (expr, cost) := extractWithCost g_sat rootId query.hw
  -- 5. Query bound from relational saturation
  let outputBound := queryBound g_sat rootId
  ⟨cost, inferReduction expr, outputBound⟩
```

The algorithmic e-graph uses these responses as edge weights in its own extraction.

**De-risk**: If the full protocol is too complex, use a precomputed lookup table:
- For each (butterfly_type × field × hardware), precompute the cost offline
- Store as a `HashMap` in the algorithmic extraction
- Still verified (each entry proven correct), just not dynamically computed

Create: `AmoLean/EGraph/Verified/Matrix/CrossEGraphProtocol.lean`

**N24.5 — Composition theorems** (CRÍTICO, 800 LOC, HIGH risk)

The crown jewel: if each butterfly is semantically correct, the entire NTT is correct.

```lean
-- If each stage preserves the NTT semantics, the composed NTT is correct
theorem ntt_composition_sound
    (plan : NTTPlan)
    (hStages : ∀ i, i < plan.stages.size →
      stageSemantics (plan.stages[i]!) plan.size plan.field =
      ntt_stage_spec i plan.size plan.field)
    (input : Array (ZMod plan.field)) :
  evalNTTPlan plan input = ntt_spec plan.field input

-- Bridge to arithmetic level: optimized butterfly = spec butterfly
theorem optimized_butterfly_correct
    (resp : ArithmeticCostResponse) (query : ArithmeticCostQuery)
    (hQuery : queryArithmeticCost g query = resp) :
  ∀ a w b, evalOptimizedButterfly resp a w b query.field =
           butterflySpec query.butterflyType a w b query.field
```

These compose with the extraction soundness theorems from both e-graphs to give the master theorem:

```lean
theorem ultra_joint_optimization_sound
    (matEGraph : EGraph MatENodeOp)
    (mixedEGraph : MultiRelMixed)
    (hw : HardwareCost) (cache : CacheConfig)
    (hExtract : extractOptimalPlan matEGraph mixedEGraph hw cache = some plan) :
  ∀ input, evalNTTPlan plan input = ntt_spec plan.field input
```

Create: `AmoLean/EGraph/Verified/Matrix/CompositionTheorems.lean`

### SPIRAL Comparison

| Aspect | SPIRAL | Truth Ultra (Phase 24) |
|--------|--------|----------------------|
| Algorithmic search | DP over rule trees | E-graph saturation over MatExpr |
| Implementation search | Code generation + measurement | E-graph saturation over MixedNodeOp |
| Cross-level coupling | Generate → compile → measure → feedback | Cross-e-graph cost query (no compilation) |
| Verification | None (HELIX post-hoc) | Built-in (each rule is a theorem) |
| Optimality guarantee | Heuristic (DP relaxation) | Optimal within represented space |
| Hardware adaptation | ISA database + empirical tuning | HardwareCost struct + cost function |

---

## Phase 25: Colors + Ruler (~1,500 LOC, 5 files)

### Motivation

Colors enable hardware-specific rules without rule explosion. Ruler discovers new optimization rules automatically. Together, they make the system self-improving.

### DAG

```
N25.1 ColorTypes adaptation (FUND, 300 LOC, LOW) ← depends on Phase 22
  → N25.2 ColoredMixedSpec (CRIT, 350 LOC, MED)
    → N25.3 Hardware color rules (PAR, 250 LOC, LOW)
    → N25.4 Ruler CVec for MixedNodeOp (PAR, 350 LOC, MED)
      → N25.5 Ruler integration (HOJA, 250 LOC, MED) ← de-risk gate
```

### Node Details

**N25.1 — ColorTypes adaptation** (FUNDACIONAL, 300 LOC, LOW risk)

Copy from `~/Documents/claudio/optisat/LambdaSat/ColorTypes.lean` (268 LOC). Define hardware colors:

```lean
-- Color hierarchy for NTT optimization:
-- root (0): universal rules (all targets)
--   ├── colorScalar (1): scalar-only rules
--   ├── colorSimd (2): SIMD-specific rules
--   │   ├── colorNeon (3): ARM NEON rules
--   │   └── colorAvx2 (4): x86 AVX2 rules
--   └── colorLargeArray (5): N > cacheThreshold rules
```

**N25.3 — Hardware color rules** (PARALELO, 250 LOC, LOW risk)

```lean
-- Under colorSimd: Montgomery stays in u32 lanes, no widening
coloredRule (color := colorSimd) :
  reduceGate(x, p) = montyReduce(x, p, mu)

-- Under colorScalar: Solinas fold is cheaper (no lane overhead)
coloredRule (color := colorScalar) :
  reduceGate(x, p) = solinasFold(x, p)

-- Under colorLargeArray: Montgomery preferred (cache pressure of u64)
coloredRule (color := colorLargeArray) :
  reduceGate(x, p) = montyReduce(x, p, mu)
```

**N25.4 — Ruler CVec for MixedNodeOp** (PARALELO, 350 LOC, MED risk)

Adapt OptiSat's CVecEngine. Currently Nat-specific; needs ZMod p evaluation:

```lean
-- CVec evaluation for field arithmetic
def evalMixedCVec (p : Nat) (testInputs : Array (Nat → Nat))
    (pattern : Pattern MixedNodeOp) : CVec :=
  testInputs.map (fun input =>
    evalPattern pattern (fun witnessId => input witnessId % p))
```

Multi-mode matching for field arithmetic:
- `CVecMatchMode.eq`: standard equivalence (Solinas ≡ Montgomery mod p)
- `CVecMatchMode.le`: bound discovery (solinasFold(x) ≤ 2p)
- `CVecMatchMode.modN p`: equivalence modulo p

**Discovery targets**:
- `x * (2^24 - 1) = (x << 24) - x` for KoalaBear
- `fold(fold(x)) ≡ fold(x)` (idempotent second fold)
- Fusion: `fold(a + fold(w*b))` simplification

**N25.5 — Ruler integration** ⚠ de-risk gate (HOJA, 250 LOC, MED risk)

If SelfImprovement loop doesn't converge or discovers too many spurious rules, fall back to manually writing the 5-10 most impactful rules (shift-decomposition, fold fusion, lazy reduction bounds).

---

## Phase 26: Cost Architecture (~1,550 LOC, 5 files)

### Motivation

The current cost model (`HardwareCost`) only knows ALU latencies. Our architectural analysis identified that different cost concerns live at different levels. Phase 26 implements this separation cleanly.

### What goes WHERE (the key insight)

| Concern | Level | Why | Implementation |
|---------|-------|-----|----------------|
| ALU latency per op | Level 3 (Cost fn) | Per-node, hardware-parametric | `HardwareCost` ← already exists |
| Branch penalty | Level 3 (Cost fn) | Per-node, informed by Level 2 bounds | `HardwareCost.branchCost(boundK)` ← enhance |
| SIMD widening | Level 3 (Cost fn) | Per-node, target-specific | `HardwareCost.wideningPenalty` ← exists |
| Energy per op | Level 3 (Cost fn) | Per-node, hardware-parametric | `HardwareCost.energyCost` ← new field |
| Register pressure | Level 4 (Extraction) | Per-subtree, depends on evaluation order | `EnhancedCostModel` ← exists |
| Cache/memory | Level 1 (NTTPlan) | Per-NTT, depends on access pattern | `planCacheCost` ← Phase 23 |
| ILP (critical path) | Level 4 (Extraction) | Global graph property, not per-node | ILP-aware extraction ← new |
| Instruction ordering | Level 5 (Scheduling) | Post-extraction, target-specific | Scheduler ← new |

### DAG

```
N26.1 HardwareCost enrichment (FUND, 150 LOC, LOW)
N26.2 Bound-informed branch cost (PAR, 200 LOC, MED) ← depends on Phase 22
N26.3 ILP-aware extraction (CRIT, 500 LOC, HIGH) ← depends on Phase 24
N26.4 Post-extraction scheduler (PAR, 500 LOC, MED)
N26.5 Integration (HOJA, 200 LOC, MED)
```

### Node Details

**N26.1 — HardwareCost enrichment** (FUNDACIONAL, 150 LOC, LOW risk)

```lean
-- Add to existing HardwareCost:
structure HardwareCost where
  -- ... existing fields ...
  -- NEW:
  energyMul : Nat := 10        -- picojoules per multiply
  energyAdd : Nat := 1         -- picojoules per add
  energyShift : Nat := 1       -- picojoules per shift
  branchMispredictCost : Nat := 12  -- cycles per mispredict
  branchPredictability : Nat := 90  -- % (90 = highly predictable for NTT)
```

**N26.2 — Bound-informed branch cost** (PARALELO, 200 LOC, MED risk)

The bridge between Level 2 (e-graph bounds) and Level 3 (cost function):

```lean
-- Instead of: branchPenalty * numBranches (hack)
-- Now:        informed branch cost from bounds
def informedBranchCost (hw : HardwareCost) (boundK : Nat) : Nat :=
  let numBranches := if boundK ≤ 1 then 0
                     else if boundK ≤ 2 then 1
                     else Nat.log2 boundK
  let mispredictProb := (100 - hw.branchPredictability)
  numBranches * (hw.branchMispredictCost * mispredictProb / 100)
```

**N26.3 — ILP-aware extraction** (CRÍTICO, 500 LOC, HIGH risk)

Standard greedy extraction minimizes `Σ costs`. For ILP-sensitive code, what matters is the critical path depth:

```lean
-- Extraction objective: minimize max(critical_path, total_ops / issue_width)
structure ILPExtractionConfig where
  issueWidth : Nat := 4        -- instructions per cycle (ARM Cortex-A76)
  pipelineDepth : Nat := 11    -- pipeline stages

def ilpAwareCost (node : MixedNodeOp) (childCosts : List (Nat × Nat))
    (hw : HardwareCost) : Nat × Nat :=  -- (total_cost, critical_path_depth)
  let opCost := mixedOpCost hw node
  let totalCost := opCost + childCosts.foldl (·.1 + ·.1) 0
  let critPath := opCost + childCosts.foldl (fun acc c => max acc c.2) 0
  (totalCost, critPath)
```

This changes extraction to be Pareto-aware: among expressions with equal total cost, prefer those with shorter critical paths.

**N26.4 — Post-extraction scheduler** (PARALELO, 500 LOC, MED risk)

Extends existing `InstructionScheduling.lean` (365 LOC):

```lean
-- List scheduling with latency model
def scheduleBlock (instrs : List ScheduledInstr) (hw : HardwareCost) : List ScheduledInstr :=
  -- 1. Build dependency DAG
  -- 2. Compute earliest-start-time for each instruction
  -- 3. Greedily schedule: pick ready instruction with highest latency-to-end
  -- 4. Track register liveness; insert spills if needed
  ...
```

The scheduler operates AFTER extraction — it doesn't change WHAT is computed, only IN WHAT ORDER.

---

## Phase 27: Pipeline + Benchmarks (~1,200 LOC, 3 files)

### Master Theorem

```lean
theorem ultra_pipeline_soundness
    [Inhabited (ZMod p)] [Fact (Nat.Prime p)]
    (matEGraph : EGraph MatENodeOp)
    (mixedEGraph : MultiRelMixed)
    (hw : HardwareCost) (cache : CacheConfig)
    -- Phase 24: joint extraction produces a plan
    (hPlan : extractOptimalPlan matEGraph mixedEGraph hw cache = some plan)
    -- Phase 22: relational saturation preserved bounds
    (hBounds : MRCV mixedEGraph.baseGraph mixedEGraph.boundDag env v)
    -- Phase 23: plan stages are well-formed
    (hWF : plan.wellFormed) :
    -- Conclusion: optimized NTT = specification NTT
    ∀ input : Array (ZMod p),
      evalOptimizedNTT plan hw input = ntt_spec p input
```

Composition chain:
1. Phase 24 `ultra_joint_optimization_sound` → plan is semantically correct
2. Phase 22 `saturateColoredF_preserves_MRCV` → bounds are valid
3. Phase 23 `nttPlan_semantic_preservation` → plan execution = NTT spec
4. Existing `pipeline_mixed_equivalent` → arithmetic optimization is sound
5. Existing `mixed_extractable_sound` → extraction is sound
6. Existing `lowerMixedExprToLLE_evaluates` → lowering to Trust-Lean is sound

### Benchmark Targets

| Field | Today | Target (Ultra) | Mechanism |
|-------|-------|----------------|-----------|
| BabyBear NTT (N=2^20) | +15-20% vs Plonky3 | **+25-35%** | Radix-4 + lazy reduction + cache-aware |
| Goldilocks NTT (N=2^20) | +17-31% vs Plonky3 | **+20-35%** | Per-stage Solinas/Montgomery + lazy |
| KoalaBear NTT (N=2^20) | +15-20% vs Plonky3 | **+20-30%** | Shift-decomposition + lazy reduction |
| BabyBear scalar butterfly | +58% vs Plonky3 | **+60-70%** | Bound-informed branch elimination |
| Multi-field adaptive | N/A | **NEW** | Ruler discovers field-specific rules |

### DAG

```
N27.1 ultra_pipeline_soundness (CRIT, 400 LOC, MED)
N27.2 Rust benchmark suite (PAR, 500 LOC, LOW)
N27.3 Comparison harness (HOJA, 300 LOC, LOW)
```

---

## Risk Mitigation Summary

| Risk | Phase | Severity | Mitigation |
|------|-------|----------|------------|
| Type cascade (52 importers of MixedNodeOp) | ALL | CRITICAL | Adaptor pattern, NEVER modify MixedNodeOp |
| MixedEMatchSoundness regression | ALL | CRITICAL | Never touched. MRCV sits above e-match layer |
| MRCV preservation intractable | 22 | HIGH | Fall back to advisory bounds (not verified) |
| Radix-4 correctness bridge | 23 | HIGH | Reduce to 2× radix-2 (standard factorization) |
| MatENodeOp semantics too complex | 24 | HIGH | Option A (semantic labels) vs Option B (matrices) |
| Cross-e-graph protocol too slow | 24 | HIGH | Precomputed lookup table (still verified) |
| Composition theorem too deep | 24 | HIGH | Factor into per-stage lemmas + induction |
| Ruler discovers spurious rules | 25 | MED | Fall back to manual rules (5-10 key ones) |
| ILP extraction changes results | 26 | MED | Pareto-aware: never worse than greedy |
| E-graph explosion | ALL | MED | TieredSatConfig: eq every 1, rel every 5, cross every 10 |

---

## Totals

| | Phase 22 | Phase 23 | Phase 24 | Phase 25 | Phase 26 | Phase 27 | Total |
|---|---------|---------|---------|---------|---------|---------|-------|
| New files | 7 | 6 | 8 | 5 | 5 | 3 | **34** |
| LOC (new) | ~1,030 | ~1,850 | ~3,200 | ~1,200 | ~1,550 | ~1,200 | **~10,030** |
| LOC (copy/adapt) | ~1,170 | ~200 | ~0 | ~300 | ~0 | ~0 | **~1,670** |
| LOC total | ~2,200 | ~2,050 | ~3,200 | ~1,500 | ~1,550 | ~1,200 | **~11,700** |
| Theorems (est.) | ~15 | ~12 | ~25 | ~12 | ~8 | ~5 | **~77** |
| Modified existing | 0 | 1 | 0 | 0 | 1 | 0 | **2** |
| Sorry target | 0 | 0 | 0 | 0 | 0 | 0 | **0** |

---

## Critical Files NOT to Modify

- `MixedNodeOp.lean` (503 LOC) — 52 importers
- `MixedEMatchSoundness.lean` (1,918 LOC) — most fragile proof
- `MixedSemanticSpec.lean` (175 LOC) — CV definition
- `MixedPipeline.lean` (246 LOC) — existing pipeline_mixed_equivalent theorem
- `PipelineSoundness.lean` — master theorem (Level 2 only)

## Source Files to Copy/Adapt from OptiSat v2

| OptiSat file | → AMO-Lean target | Phase |
|---|---|---|
| `LambdaSat/RelationTypes.lean` | N22.1 RelationTypes | 22 |
| `LambdaSat/DirectedRelSpec.lean` | N22.2 DirectedRelSpec | 22 |
| `LambdaSat/MultiRelEGraph.lean` | N22.3 MultiRelMixed | 22 |
| `LambdaSat/MultiRelSaturate.lean` | N22.4 TieredSaturation | 22 |
| `LambdaSat/MultiRelSoundness.lean` | N22.7 Backward compat | 22 |
| `LambdaSat/ColorTypes.lean` | N25.1 ColorTypes | 25 |
| `LambdaSat/ColoredMerge.lean` | N25.2 ColoredMixedSpec | 25 |
| `LambdaSat/Ruler/CVecEngine.lean` | N25.4 Ruler CVec | 25 |
| `LambdaSat/Ruler/SelfImprovement.lean` | N25.5 Ruler integration | 25 |

## Verification Chain

Each phase contributes one link to the end-to-end soundness chain:

```
Phase 22: saturateColoredF_preserves_MRCV
    ↓ (bounds are valid)
Phase 23: nttPlan_semantic_preservation
    ↓ (plan execution = NTT spec)
Phase 24: ultra_joint_optimization_sound + optimized_butterfly_correct
    ↓ (joint extraction preserves semantics)
Phase 25: CCV_implies_base_CV (backward compat)
    ↓ (colored rules don't break base soundness)
Phase 26: ilpAwareCost_preserves_semantics (extraction doesn't change meaning)
    ↓ (only changes WHICH equivalent is chosen)
Phase 27: ultra_pipeline_soundness (composition of above)
    ↓
Existing: pipeline_mixed_equivalent → mixed_extractable_sound →
          lowerMixedExprToLLE_evaluates → Trust-Lean CBackend
```

`lake build` 0 errors after each node. `#print axioms` 0 custom axioms on master theorem.

---

## Why This Hasn't Been Done Before

1. **SPIRAL** (CMU, 1998-present): Multi-level optimization but zero verification. Rule correctness is assumed, not proved. HELIX certifies SPIRAL's output post-hoc in Coq, but doesn't build the optimizer inside the proof assistant.

2. **Fiat-Crypto** (MIT, 2019-present): Verified arithmetic generation but no algorithmic optimization. Given a fixed algorithm (e.g., Montgomery multiplication), it generates verified code. It doesn't choose WHICH algorithm.

3. **egg/eqsat** (UW, 2020-present): Equality saturation for compiler optimization but single-level. One e-graph, one cost function. No cross-level queries.

4. **Diospyros** (Cornell, 2021): Equality saturation for DSP vectorization but unverified. Uses egg to find good SIMD schedules but has no formal correctness guarantee.

5. **lean-egg** (POPL 2026): Bridges egg and Lean but for term rewriting, not signal processing. Translation validation pattern (egg proposes, Lean verifies).

Truth Ultra combines:
- SPIRAL's multi-level architecture (algorithmic + arithmetic)
- egg's equality saturation (non-destructive search)
- OptiSat v2's relational saturation (bounds, colors, auto-discovery)
- Lean 4's proof kernel (every step verified)
- Cross-e-graph protocol (novel — no prior system does this)

The result: the first system that **jointly optimizes algorithmic structure and arithmetic implementation with formal verification of every decision**.
