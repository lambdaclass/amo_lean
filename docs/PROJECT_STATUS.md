# AMO-Lean: Project Status

*Last Updated: January 23, 2026 - Phase 2 (E-Graph) Completed*

---

## Current Capabilities

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         AMO-Lean Pipeline                                   │
│                                                                             │
│  Expr α ──→ E-Graph Saturation ──→ Best Expr ──→ C Code                    │
│                                                                             │
│  (x+0)*1+y*0  ──→  equality saturation  ──→  x  ──→  int64_t f() {         │
│                    with cost model              return x;                   │
│                                                 }                           │
└─────────────────────────────────────────────────────────────────────────────┘
```

### What It Can Do

1. **Expression AST** (`Expr α`): constants, variables, addition, multiplication
2. **Denotational Semantics**: `denote` connects syntax with Mathlib semantics
3. **Greedy Rewriter**: 8 verified rewrite rules, bottom-up to fixpoint
4. **E-Graph with Equality Saturation**: Full implementation with extraction
5. **C Code Generation**: with let-lifting (SSA form)
6. **Mathlib Integration**: for algebraic types (Semiring, Ring)
7. **0 `sorry`** in greedy rewriter proofs - fully verified

---

## Project Structure

```
amo-lean/
├── AmoLean.lean                 # Main module, public API
├── AmoLean/
│   ├── Basic.lean               # AST, rules, greedy rewriter, CostModel
│   ├── Correctness.lean         # Soundness proofs (0 sorry)
│   ├── MathlibIntegration.lean  # Mathlib integration
│   ├── CodeGen.lean             # C code generation
│   └── EGraph/
│       ├── Basic.lean           # E-graph structures, union-find (~530 lines)
│       ├── EMatch.lean          # Patterns, e-matching, rules (~275 lines)
│       └── Saturate.lean        # Saturation, extraction (~190 lines)
├── docs/
│   ├── BENCHMARK_FASE1.md       # Performance analysis
│   ├── PROJECT_STATUS.md        # This file
│   └── ESTADO_PROYECTO.md       # Spanish version
├── ROADMAP.md                   # Detailed roadmap
└── lakefile.lean                # Project configuration
```

---

## Completed Phases

### Phase 1: Toy Model ✓

- [x] `Expr α` inductive type for arithmetic expressions
- [x] Denotational semantics
- [x] 8 rewrite rules (identities, annihilators, distributivity)
- [x] Bottom-up rewriter with fixpoint iteration
- [x] Basic C code generation

### Phase 1.5: Complete Verification ✓

- [x] Remove `partial` from `rewriteBottomUp` (structural recursion)
- [x] Remove `partial` from `rewriteToFixpoint` (pattern matching on Nat)
- [x] Prove `rewriteBottomUp_sound` by induction on `Expr`
- [x] Prove `rewriteToFixpoint_sound` by induction on `fuel`
- [x] Prove `simplify_sound`
- [x] **Result: 0 `sorry` in project**

### Phase 1.75: Pre-E-Graph Optimizations ✓

- [x] Benchmark baseline (253k nodes in 0.5s, O(n) scaling)
- [x] Cost Model: `CostModel` and `exprCost`
- [x] Constant Folding: `rule_const_fold_add`, `rule_const_fold_mul`
- [x] Associativity evaluation (rejected: 70x slowdown in greedy)
- [x] `simplifyWithConstFold` - recommended function
- [x] Documentation: `docs/BENCHMARK_FASE1.md`

### Phase 2: E-Graph and Equality Saturation ✓

**Data Structures:**
- [x] `EClassId`: Array index (Nat)
- [x] `ENodeOp`: Operations with child IDs (non-recursive)
- [x] `ENode`: Wrapper with helpers
- [x] `EClass`: Equivalence class with nodes and cost metadata
- [x] `UnionFind`: Path compression with `Array EClassId`
- [x] `EGraph`: Main structure (union-find + hashcons + classes)

**Algorithms:**
- [x] `add(EGraph, ENode) → (EClassId, EGraph)` - Add with deduplication
- [x] `merge(EGraph, EClassId, EClassId) → EGraph` - Union classes
- [x] `find(EGraph, EClassId) → EClassId` - Find canonical
- [x] `rebuild(EGraph) → EGraph` - Full re-canonicalization
- [x] `canonicalize` - Normalize node children

**E-Matching:**
- [x] `Pattern` - Patterns with variables (`?a`, `?b`, etc.)
- [x] `Substitution` - Variable to e-class mapping
- [x] `ematch` - Search for instances in an e-class
- [x] `searchPattern` - Search entire graph
- [x] `instantiate` - Create nodes from pattern + substitution

**Rewrite Rules:**
- [x] `basicRules`: `a+0→a`, `0+a→a`, `a*1→a`, `1*a→a`, `a*0→0`, `0*a→0`
- [x] `extendedRules`: + distributivity and factorization

**Saturation:**
- [x] `SaturationConfig` - Configurable limits
- [x] `saturateStep` - One iteration (apply rules + rebuild)
- [x] `saturate` - Until fixpoint or limit
- [x] `saturateAndExtract` - Saturate + compute costs + extract

**Extraction:**
- [x] `EGraphCostModel` - Cost model for E-graph
- [x] `computeCosts` - Bottom-up iterative calculation
- [x] `extract` - Extract best term from e-class

**Tests (all pass):**
```
x + 0           → x          ✓
x * 1           → x          ✓
(x + 0) * 1     → x          ✓
(x + y) * 0     → 0          ✓
x*1 + 0         → x          ✓ (1 iteration)
x * (y + z)     → explored   ✓ (2 iterations, 8 nodes)
```

---

## Usage Examples

### Greedy Rewriter
```lean
import AmoLean

open AmoLean Expr

-- Simple expression
let expr := add (mul (var 0) (const 1)) (const 0)  -- x*1 + 0
let simplified := simplify expr                      -- x
```

### E-Graph Optimizer
```lean
import AmoLean.EGraph.Saturate

open AmoLean.EGraph

-- Optimize with basic rules
let expr := Expr.add (Expr.mul (Expr.var 0) (Expr.const 1)) (Expr.const 0)
match optimizeBasic expr with
| some result => -- result = Expr.var 0
| none => -- error

-- Optimize with extended rules (distributivity)
let result := optimizeExtended expr

-- Custom configuration
let config := { maxIterations := 50, maxNodes := 5000 }
let (result, satResult) := optimize expr RewriteRule.basicRules config
-- satResult.iterations, satResult.saturated, satResult.reason
```

### C Code Generation
```lean
import AmoLean

let expr := Expr.mul (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.var 2)
let code := exprToC "my_func" ["x", "y", "z"] expr
-- "int64_t my_func(int64_t x, int64_t y, int64_t z) { ... }"
```

---

## Pending Phases

### Phase 3: Extended Mathlib on E-Graph

- [ ] Macro `#compile_rules` for automatic extraction
- [ ] New rules from Mathlib (commutativity, associativity)
- [ ] E-class analysis for instance synthesis

### Phase 4: Cryptographic Applications (FRI)

- [ ] Finite field arithmetic (`ZMod p`, `GF(2^n)`)
- [ ] Polynomial evaluation
- [ ] FFT as operation composition
- [ ] Automatic optimization discovery
- [ ] Rust code generation

---

## Architecture: Toy Model ↔ Full FRI Optimizer

```
┌────────────────────────────────────────────────────────────────────────┐
│                         ABSTRACTION LEVELS                             │
├────────────────────────────────────────────────────────────────────────┤
│                                                                        │
│  Level 4: Complete FRI Protocol                                        │
│           ├── Merkle commitments                                       │
│           ├── Folding rounds                                           │
│           └── Proximity verification                                   │
│                           ↑                                            │
│  Level 3: Polynomial Operations                                        │
│           ├── Verified FFT/NTT                                         │
│           ├── Interpolation                                            │
│           └── Multi-point evaluation                                   │
│                           ↑                                            │
│  Level 2: Finite Field Arithmetic                                      │
│           ├── F_p (prime field)                                        │
│           ├── Field extensions                                         │
│           └── Montgomery/Barrett operations                            │
│                           ↑                                            │
│  Level 1: Arithmetic Expressions  ◄──── WE ARE HERE (E-Graph ready)   │
│           ├── Generic AST                                              │
│           ├── E-graph saturation                                       │
│           └── Code generation                                          │
│                                                                        │
└────────────────────────────────────────────────────────────────────────┘
```

---

## Problem History and Solutions

| Problem | Cause | Solution |
|---------|-------|----------|
| Lean 4.3.0 incompatible | Mathlib requires recent versions | Updated to 4.16.0 |
| `leanOptions` doesn't exist | Lake API changed | New lakefile syntax |
| `BEq` vs `Eq` in proofs | Rules use `==` but proofs need `=` | `LawfulBEq` + lemmas |
| `partial` blocks induction | Lean doesn't generate induction principle | **SOLVED**: Structural recursion + `termination_by` |
| Associativity slowdown | 70x slower due to repeated applications | **SOLVED**: Validated need for E-graphs |
| E-graph memory | Recursive types cause GC issues | **SOLVED**: Flat structures (Array + HashMap) |

---

## Lessons Learned

### From Phase 1.75 (Benchmark)
- **Greedy is fast but limited**: 253k nodes in 0.5s, but doesn't explore alternatives
- **Associativity breaks greedy**: 70x slowdown because it applies rules indefinitely
- **Cost model is essential**: Without it, no criterion for "better"

### From Phase 2 (E-Graph)
- **Flat structures work**: `Array` + `HashMap` avoid GC problems
- **Rebuild is critical**: Without re-canonicalization, hashcons becomes inconsistent
- **E-matching is elegant**: Patterns + substitutions = declarative search

---

## Complexity Estimate

```
                        Complexity     Status           Dependencies
                        ──────────     ──────           ────────────
Phase 1: Toy Model      ████░░░░░░     ✅ COMPLETED     None
Phase 1.5: Verification ████░░░░░░     ✅ COMPLETED     Toy Model
Phase 1.75: Pre-E-graph ████░░░░░░     ✅ COMPLETED     Verification
Phase 2: E-graph        █████░░░░░     ✅ COMPLETED     Pre-E-graph
Phase 3: Mathlib Ext    █████░░░░░     🔜 Planned       E-graph
Phase 4: Finite Field   ██████░░░░     🔜 Planned       Mathlib ZMod
Phase 5: FFT            ███████░░░     🔜 Planned       Finite Field
Phase 6: FRI            █████████░     🔜 Planned       All above
Phase 7: CodeGen        ██████████     🔜 Planned       FRI
Phase 8: Production     ██████████     🔜 Planned       Everything
```

---

## References

1. Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. Sun et al. "E-Graphs as Circuits, and Optimal Extraction via Treewidth" (2024)
3. Gross et al. "Accelerating Verified-Compiler Development with a Verified Rewriting Engine" (ITP 2022)
4. Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic" (Fiat-Crypto)
5. Metaprogramming in Lean 4 (official documentation)

---

*Document generated: January 2026*
*Last update: January 23, 2026 - Phase 2 (E-Graph) completed*
