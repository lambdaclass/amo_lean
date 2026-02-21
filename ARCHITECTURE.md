# AMO-Lean: Architecture

## Current Version: v2.2.0

## Project Structure (v2.2.0)

```
amo-lean/
├── AmoLean/                    # Lean source (~41,700 LOC, 97 files)
│   ├── NTT/                    # NTT specification + proofs
│   │   ├── Spec.lean           # O(N^2) reference specification
│   │   ├── CooleyTukey.lean    # O(N log N) verified algorithm
│   │   ├── Butterfly.lean      # Butterfly operation proofs
│   │   ├── LazyButterfly.lean  # Harvey optimization (lazy reduction)
│   │   ├── Correctness.lean    # Main equivalence theorems + INTT roundtrip
│   │   ├── ListFinsetBridge.lean # List<->Finset bridge (0 axioms)
│   │   ├── BabyBear.lean       # BabyBear NTT (0 sorry)
│   │   └── Radix4/             # Verified radix-4 implementation
│   ├── Field/                  # Field implementations (0 axioms, 0 sorry)
│   │   ├── Goldilocks.lean     # Goldilocks (p = 2^64 - 2^32 + 1)
│   │   └── BabyBear.lean       # BabyBear (p = 2^31 - 2^27 + 1)
│   ├── EGraph/                 # E-Graph optimization engine
│   │   ├── Optimize.lean       # Equality saturation (unverified, deprecated)
│   │   ├── VerifiedRules.lean  # 19/20 rules with formal proofs
│   │   └── Verified/           # Verified e-graph engine (121 theorems, 0 sorry)
│   │       ├── UnionFind.lean  # Verified union-find (43 theorems)
│   │       ├── CoreSpec.lean   # Hashcons + merge invariants (78 theorems)
│   │       ├── Bridge.lean     # Expr Int ↔ CircuitNodeOp adapter
│   │       ├── Rules.lean      # 10 verified rules wired to Bridge
│   │       └── Optimize.lean   # Verified optimization pipeline
│   ├── FRI/                    # FRI protocol components (0 sorry)
│   ├── Bridge/                 # Trust-Lean bridge (26 theorems, 0 sorry)
│   │   └── TrustLean.lean      # Verified type conversion + roundtrip + pipeline
│   ├── Sigma/                  # Sigma-SPL IR definitions
│   ├── Matrix/                 # Matrix algebra + permutations
│   ├── Verification/           # Correctness proofs
│   │   ├── AlgebraicSemantics.lean  # Lowering correctness (~5,700 LOC, 0 sorry)
│   │   ├── FRI_Properties.lean      # FRI folding proofs (0 sorry)
│   │   └── Poseidon_Semantics.lean  # Poseidon2 verification (12 sorry, test-backed)
│   └── Backends/               # Code generation (C, Rust)
│
├── generated/                  # Generated C code
│   ├── field_goldilocks.h      # Goldilocks arithmetic (scalar)
│   ├── field_goldilocks_avx2.h # Goldilocks arithmetic (AVX2)
│   ├── ntt_kernel.h            # Lazy butterfly kernel
│   ├── ntt_context.h           # NTT context with caching
│   └── poseidon2_bn254_t3.h    # Poseidon2 hash
│
├── libamolean/                 # Distributable header-only C library
├── verification/plonky3/       # Plonky3 verification suite (Rust FFI)
├── Tests/                      # Test suites (2850+ tests)
└── docs/                       # Documentation
    ├── BENCHMARKS.md            # Full benchmark report
    └── project/                 # Design decisions, progress logs
```

## Verification Status (v2.2.0)

### Formal Proofs (Lean 4)

| Component | Status | Sorry | Axioms | Detail |
|-----------|--------|-------|--------|--------|
| NTT Radix-2 (CooleyTukey + INTT roundtrip) | **100%** | 0 | 0 | Fully proven incl. bridge |
| NTT Radix-4 | Interface | 0 | 8 | Opaque functions + properties |
| FRI (Folding + Merkle) | **100%** | 0 | 0 | Fully proven |
| Matrix/Perm | **100%** | 0 | 1 | Match splitter limitation |
| E-Graph Rewrite Rules | **95%** | 0 | 0 | 19/20 rules verified |
| **E-Graph Verified Engine** | **100%** | **0** | **0** | **121 theorems, 4,594 LOC** |
| **Trust-Lean Bridge** | **100%** | **0** | **0** | **26 theorems, 544 LOC, roundtrip + injectivity** |
| Goldilocks Field | **100%** | 0 | 0 | All 5 axioms eliminated |
| BabyBear Field | **100%** | 0 | 0 | All 4 axioms eliminated |
| AlgebraicSemantics | **100%** | 0 | 0 | 19/19 cases proven |
| Poseidon2 | Computational | 12 | 0 | All backed by 21 test vectors |

**Codebase**: ~41,700 LOC | **9 axioms** (8 Radix-4 + 1 Perm) | **12 active sorry** (all Poseidon, match splitter limitation) | **147 verified theorems** (121 e-graph + 26 bridge)

## Key Design Decisions (v2.2.0)

1. **Equality Saturation (E-Graphs)**: Optimization via verified rewrite rules rather than ad-hoc transformations. Every optimization is a theorem.
2. **Sigma-SPL Algebraic IR**: Matrix expressions lowered through scatter/gather semantics. 19/19 operations formally verified.
3. **Lazy Reduction (Harvey 2014)**: Defer modular reduction in butterfly operations for reduced modular arithmetic overhead.
4. **Skeleton + Kernel Architecture**: Manual C loop structure (skeleton) with Lean-verified butterfly (kernel). Combines performance control with formal guarantees.
5. **Twiddle Factor Caching**: Pre-computed twiddle factors for all NTT layers, stored in NttContext.
6. **Nat in Lean Proofs**: Use arbitrary-precision naturals to avoid overflow reasoning during proofs. C code uses fixed-width integers with verified bounds.
7. **Goldilocks Specialization**: Exploit p = 2^64 - 2^32 + 1 structure for efficient reduction without Barrett/Montgomery.

For detailed rationale on each decision, see [docs/project/DESIGN_DECISIONS.md](docs/project/DESIGN_DECISIONS.md).

---

### Fase 10: Trust-Lean Wiring

**Goal**: Integrar Trust-Lean v1.2.0 como lake dependency de amo-lean. Crear módulo Bridge con conversión de tipos verificada (roundtrip) y pipeline end-to-end MatExpr → ExpandedSigma → TrustLean.Stmt → código C via CBackend industrial.

**Insights**: `amo_lean_v2_2_0_trust_lean_wiring_insights.md`

**Key Design Decisions**:
1. **Option type for convertScalarVar** (QA recommendation): Since `String` is infinite domain but only {"x","y","t"} are valid ExpandedSigma variable names, `convertScalarVar` returns `Option TrustLean.Bridge.ScalarVar`. Totality proven for well-formed inputs from smart constructors.
2. **Unidirectional Coe only**: `AmoLean → TrustLean` coercion only. No bidirectional Coe (causes elaborator loops per online research).
3. **Module isolation**: Only `AmoLean.Bridge.TrustLean` imports Trust-Lean. Rest of amo-lean never touches Trust-Lean types directly.
4. **Coexistence with legacy codegen**: `AmoLean/Sigma/CodeGen.lean` (unverified) stays untouched. New verified pipeline is additive.

**Files**:
- `lakefile.lean` — Add Trust-Lean dependency
- `AmoLean/Bridge/TrustLean.lean` — Conversion functions + proofs + pipeline
- `AmoLean/Tests/TrustLeanIntegration.lean` — Integration test suite

#### DAG (v2.2.0)

| Nodo | Tipo | Deps | Gate | Status |
|------|------|------|------|--------|
| N10.1 Lake Dependency Setup | FUND | — | `lake build` succeeds with `import TrustLean.Bridge`, 0 warnings | done |
| N10.2 Type Conversion + Roundtrip | CRIT | N10.1 | Roundtrip proven, convertScalarVar Option totality, 0 sorry | done |
| N10.3 Integration Tests + Pipeline | PAR | N10.2 | 6 constructors tested, pipeline e2e generates C, semantic equiv | done |
| N10.4 Zero Sorry Audit | HOJA | N10.3 | 0 sorry/admit/axiom in Bridge, full build clean | done |

#### Detailed Node Specifications

**N10.1 FUNDACIONAL — Lake Dependency Setup** (~20 LOC)
- Add `require "trust-lean" from git "../Trust-Lean" @ "v1.2.0"` to lakefile.lean
- Update version to v2.2.0
- Create `AmoLean/Bridge/TrustLean.lean` stub with `import TrustLean.Bridge`
- Verify `lake build` succeeds with 0 errors, 0 warnings
- lean-toolchain compatibility: both projects already at v4.26.0 (verified)

**N10.2 CRITICO — Type Conversion + Roundtrip** (~200 LOC)
- `convertScalarVar : String → Nat → Option TrustLean.Bridge.ScalarVar`
  - Maps: "x" → some ⟨.input, n⟩, "y" → some ⟨.output, n⟩, "t" → some ⟨.temp, n⟩
  - All others → none
- `convertScalarExpr : AmoLean.ScalarExpr → Option TrustLean.Bridge.ScalarExpr`
- `convertIdxExpr : AmoLean.IdxExpr → TrustLean.Bridge.IdxExpr` (direct, no Option needed)
- `convertGather / convertScatter` (direct mapping)
- `convertExpandedKernel : AmoLean.ExpandedKernel → Option TrustLean.Bridge.ExpandedKernel`
- `convertExpandedSigma : AmoLean.ExpandedSigma → Option TrustLean.Bridge.ExpandedSigma`
- `convertBack*` for roundtrip (reverse direction, total)
- **Theorems**: roundtrip_correctness, convert_injective, scalarVar_totality_wellformed
- **De-risk**: ScalarVar mapping verified safe — only {"x","y","t"} flow through ExpandedSigma smart constructors

**N10.3 PARALELO — Integration Tests + Pipeline** (~100-150 LOC)
- Test each of 6 ExpandedSigma constructors: nop, scalar, seq, par, loop, temp
- Pipeline function: `verifiedCodeGen : AmoLean.ExpandedSigma → Option String`
  - Chains: convertExpandedSigma → expandedSigmaToStmt → stmtToC
- `#eval` tests generating actual C code
- Semantic equivalence: output of verified pipeline matches expected C structure

**N10.4 HOJA — Zero Sorry Audit**
- `grep -r "sorry\|admit\|axiom" AmoLean/Bridge/` returns empty
- Full `lake build` clean (0 errors, 0 warnings)
- No `native_decide` or `simp [*]` in proofs

#### Formal Properties (v2.2.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N10.2 | Roundtrip correctness: convertBack ∘ convertExpandedSigma = id | EQUIVALENCE | P0 |
| N10.2 | Injectivity: conversion preserves distinctness | SOUNDNESS | P0 |
| N10.2 | ScalarVar totality for well-formed names {"x","y","t"} | INVARIANT | P0 |
| N10.3 | Pipeline semantic equivalence: C output matches for converted inputs | PRESERVATION | P1 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **B24 Lake + Stub**: N10.1 (SECUENCIAL) ✓
- [x] **B25 Conversion Core**: N10.2 (SECUENCIAL) ✓
- [x] **B26 Integration + Pipeline**: N10.3 (SECUENCIAL) ✓
- [x] **B27 Final Audit**: N10.4 (SECUENCIAL) ✓

#### Execution Order

```
B24 (N10.1 FUND) → B25 (N10.2 CRIT) → B26 (N10.3 PAR) → B27 (N10.4 HOJA)
```

#### Critical Lessons Applied (from insights)

- **L-310**: Cross-project lake dependencies require toolchain sync (SATISFIED: both v4.26.0)
- **L-336**: Typeclass instance resolution across projects needs explicit import paths
- **L-134**: De-risk fundacional nodes BEFORE working on dependents (ScalarVar mapping verified)
- **L-138**: NEVER defer fundacionales as tech debt

---

### Fase 10 Corrección 1: QA Follow-ups (CONDITIONAL PASS → FULL PASS)

**Goal**: Resolver 5 findings pendientes del QA review para cerrar v2.2.0 con FULL PASS.

**Insights**: `amo_lean_v2_2_0_qa_follow_ups_forward_roundtrip_injectivity_insights.md`

**Key Design Decisions**:
1. **No Mathlib `Function.IsPartialInv`**: Overhead de import innecesario. Derivar injectivity directamente del forward roundtrip (~5 LOC).
2. **`simp only [Option.bind_eq_some]` explícito**: No es `@[simp]` desde Lean 4.9. Usar siempre explícitamente.
3. **Template**: `roundtrip_scalarVar_forward` (líneas 53-68) como modelo para todos los forward roundtrips.
4. **Path dependency intencional**: Documentar en ARCHITECTURE.md que `require TrustLean from "../Trust-Lean"` es correcto para co-desarrollo monorepo.

**Files**:
- `AmoLean/Bridge/TrustLean.lean` — Forward roundtrip theorems + injectivity (~120 LOC adicionales)
- `Tests/TrustLeanIntegration.lean` — Stress test + regression (~40 LOC adicionales)

#### DAG (Corrección 1)

| Nodo | Tipo | Deps | Gate | Status |
|------|------|------|------|--------|
| N10.5 Forward Roundtrips Intermedios | CRIT | N10.2 | 5 forward theorems proven, 0 sorry | done |
| N10.6 Forward Sigma + Injectivity | CRIT | N10.5 | roundtrip_expandedSigma_forward + convert_injective proven, 0 sorry | done |
| N10.7 Stress Test + Docs | PAR | — | Stress test >100 exprs with roundtrip verification, F4 docs | done |

#### Detailed Node Specifications (Corrección 1)

**N10.5 CRITICO — Forward Roundtrips Intermedios** (~80 LOC)
- `roundtrip_scalarExpr_forward`: inducción sobre 6 constructores (var, const, neg, add, sub, mul). Cada binary op (add/sub/mul) requiere `simp only [Option.bind_eq_some]` para extraer dos sub-hipótesis + 2 IH calls.
- `roundtrip_scalarAssign_forward`: usa ScalarExpr + ScalarVar forward roundtrips.
- `roundtrip_scalarVarList_forward`: inducción sobre lista, `cases` en Option head.
- `roundtrip_scalarAssignList_forward`: inducción sobre lista.
- `roundtrip_expandedKernel_forward`: compuesto de listas + escalares.

**N10.6 CRITICO — Forward Roundtrip ExpandedSigma + Injectivity** (~50 LOC)
- `roundtrip_expandedSigma_forward`: inducción sobre 6 constructores (nop, scalar, seq, par, loop, temp). Caso `.scalar` usa ExpandedKernel forward + Gather/Scatter forwards (ya probados). Casos recursivos (seq, par, loop, temp) usan IH + forward intermedios.
- `convert_injective`: derivado directamente:
  ```lean
  cases ha : convertExpandedSigma a
  · simp [ha] at h  -- none ≠ some: contradiction
  · rw [ha] at h; have hb := h
    exact (forward a _ ha).symm.trans (forward b _ hb)
  ```

**N10.7 PARALELO — Stress Test + Docs** (~40 LOC)
- Generador programático: `buildLargeSigma : Nat → ExpandedSigma` usando `.seq` y `.loop` anidados.
- Verificación: `#eval` confirma `(convertExpandedSigma (buildLargeSigma 120)).isSome = true` + roundtrip check via `convertBack`.
- F4: Nota en ARCHITECTURE.md sobre path dependency intencional para co-desarrollo monorepo.

#### Formal Properties (Corrección 1)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N10.5 | Forward roundtrip ScalarExpr: `convertScalarExpr e = some e' → convertBackScalarExpr e' = e` | EQUIVALENCE | P0 |
| N10.5 | Forward roundtrip ExpandedKernel: same pattern | EQUIVALENCE | P0 |
| N10.6 | Forward roundtrip ExpandedSigma: `convertExpandedSigma s = some s' → convertBackExpandedSigma s' = s` | EQUIVALENCE | P0 |
| N10.6 | Injectivity: `convertExpandedSigma a = convertExpandedSigma b → a = b` | SOUNDNESS | P0 |
| N10.7 | Stress test: `(convertExpandedSigma (buildLargeSigma 120)).isSome = true` | INVARIANT | P1 |

#### Bloques (Corrección 1)

- [x] **B28 Forward Intermedios**: N10.5 (SECUENCIAL) ✓
- [x] **B29 Forward Sigma + Injectivity**: N10.6 (SECUENCIAL) ✓
- [x] **B30 Stress + Docs**: N10.7 (SECUENCIAL, parallelizable) ✓

#### Execution Order (Corrección 1)

```
B28 (N10.5 CRIT) → B29 (N10.6 CRIT)
B30 (N10.7 PAR) — paralelo, sin deps
```

#### Note on Path Dependency (F4)

The `require TrustLean from "../Trust-Lean"` path dependency is **intentional** for co-development within the same monorepo (`claudio/`). Both projects share the same git repository and are always at compatible versions. For external distribution, convert to git dependency with pinned hash. See L-357.

---

## Previous Versions

- v2.1.0: Lean 4.26 + verified e-graph engine
- v2.0.0: Major restructuring
- v1.1.0: FRI verified
- v1.0.0: Initial release

---

## Lessons (current)

Project-specific lessons learned during current version.
Generalized lessons should be migrated to `~/Documents/claudio/lecciones/lean4/`.

### v2.2.0 (Trust-Lean Wiring)

- **L-357**: Path dependencies in lake-manifest.json are not reproducible across machines
- **L-358**: Backward roundtrip easier but forward roundtrip is what rubric demands
- **L-359**: Injectivity of partial conversions requires forward roundtrip as lemma
- **L-360**: Custom recursive list conversions avoid List.mapM accumulator mismatch
- **L-361**: Test files must be registered in lakefile roots for CI visibility
- **L-362**: Section headers are not docstrings for individual declarations
- **L-363**: cases-on-Option pattern for do-notation proofs (use explicit `cases` not `split <;> simp_all`)
- **L-364**: `Option.bind_eq_some` requires explicit `simp only` since Lean 4.9
- **L-365**: Injectivity of partial functions requires some-witness formulation
- **L-366**: QA totality finding for intentionally partial conversions — reject when partiality is by design
