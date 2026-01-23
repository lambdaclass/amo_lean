# AMO-Lean: Project Status

*Last Updated: January 23, 2026 - Phase 4 (Power Extension + ZMod) Completed*

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

1. **Expression AST** (`Expr α`): constants, variables, addition, multiplication, **power**
2. **Denotational Semantics**: `denote` connects syntax with Mathlib semantics
3. **Greedy Rewriter**: 12 verified rewrite rules, bottom-up to fixpoint
4. **E-Graph with Equality Saturation**: Full implementation with extraction
5. **C Code Generation**: with let-lifting (SSA form) and power support
6. **Mathlib Integration**: for algebraic types (Semiring, Ring)
7. **`#compile_rules` Macro**: Extract rewrite rules from Mathlib theorems
8. **0 `sorry`** in greedy rewriter proofs - fully verified

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
│   ├── Meta/
│   │   └── CompileRules.lean    # #compile_rules macro
│   └── EGraph/
│       ├── Basic.lean           # E-graph structures, union-find (~530 lines)
│       ├── EMatch.lean          # Patterns, e-matching, rules (~400 lines)
│       └── Saturate.lean        # Saturation, extraction (~190 lines)
├── Tests/
│   ├── ZModDemo.lean            # ZMod finite field tests
│   └── GenericsAudit.lean       # Generics verification
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

**Tests (all pass):**
```
x + 0           → x          ✓
x * 1           → x          ✓
(x + 0) * 1     → x          ✓
(x + y) * 0     → 0          ✓
x*1 + 0         → x          ✓ (1 iteration)
x * (y + z)     → explored   ✓ (2 iterations, 8 nodes)
```

### Phase 3: Extended Mathlib on E-Graph ✓

- [x] New rules from Mathlib (commutativity, associativity):
  - `addComm`, `mulComm` (2 rules)
  - `addAssocRight`, `addAssocLeft`, `mulAssocRight`, `mulAssocLeft` (4 rules)
- [x] Rule collections: `commRules`, `assocRules`, `semiringRules` (15 total)
- [x] Helper functions in `MathlibToEGraph` namespace
- [x] Optimization to avoid redundant merges in `applyRuleAt`
- [x] **`#compile_rules` macro** - Automatic rule extraction from Mathlib theorems
  - Converts `Lean.Expr` to `Pattern` using metaprogramming
  - Supports `Add.add`, `HAdd.hAdd`, `Mul.mul`, `HMul.hMul`, `OfNat.ofNat`, `HPow.hPow`
  - File: `AmoLean/Meta/CompileRules.lean`
- [x] **Generics Audit** - Verified macro is GENERIC
  - Supports theorems with Type Classes (AddCommMagma, MulOneClass, etc.)
  - NOT limited to concrete types like Nat
  - File: `Tests/GenericsAudit.lean`

### Phase 4: Power Extension + Finite Fields ✓

**Power Extension:**
- [x] `pow` constructor added to AST: `Expr.pow : Expr α → Nat → Expr α`
- [x] `denote` updated with `[Pow α Nat]` constraint
- [x] `CostModel.powCost` added (default: 50)
- [x] `ENodeOp.pow` added to E-graph
- [x] `Pattern.pow` for E-matching
- [x] Power rules: `powZero`, `powOne`, `squareFromMul`, `squareToMul`
- [x] CodeGen generates:
  - `n=0`: literal `1`
  - `n=1`: base directly
  - `n=2`: `(x * x)` inline
  - `n>2`: `pow_int(x, n)` function call
- [x] Correctness.lean updated with pow cases

**ZMod Exploration:**
- [x] ZMod compiled and working (Mathlib.Data.ZMod.Basic)
- [x] Generic rules work in ZMod: `add_comm`, `mul_comm`, etc.
- [x] Characteristic theorems verified: `ZMod.natCast_self`
- [x] Fermat's Little Theorem verified: `ZMod.pow_card`
- [x] File: `Tests/ZModDemo.lean`

**Remaining Limitations:**
- `ZMod.natCast_self`: requires pattern matching on casts
- `ZMod.pow_card`: exponent is not a constant literal

---

## Rewrite Rules Implemented

**Greedy Rewriter:**
- `x + 0 → x`, `0 + x → x` (additive identities)
- `x * 1 → x`, `1 * x → x` (multiplicative identities)
- `x * 0 → 0`, `0 * x → 0` (annihilators)
- `a * (b + c) → a*b + a*c` (left distributivity)
- `(a + b) * c → a*c + b*c` (right distributivity)
- `const a + const b → const (a+b)` (constant folding)
- `const a * const b → const (a*b)` (constant folding)
- `a^0 → 1`, `a^1 → a` (power identities)
- `1^n → 1`, `0^n → 0` (n > 0) (special cases)

**E-Graph (additional rules):**
- `a*b + a*c → a*(b+c)` (factorization)
- `a*a → a^2` (squareFromMul)
- `a^2 → a*a` (squareToMul)

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
```

### C Code Generation
```lean
import AmoLean

let expr := Expr.pow (Expr.var 0) 2  -- x^2
let code := exprToC "square" ["x"] expr
-- "int64_t square(int64_t x) { int64_t t0 = (x * x); return t0; }"

let expr7 := Expr.pow (Expr.var 0) 7  -- x^7
let code7 := exprToC "pow7" ["x"] expr7
-- "int64_t pow7(int64_t x) { int64_t t0 = pow_int(x, 7); return t0; }"
```

### Compile Rules from Mathlib
```lean
import AmoLean.Meta.CompileRules

-- Extract rewrite rules from Mathlib theorems
#compile_rules [add_comm, mul_comm, add_zero, mul_one]
-- Output: Compiled rules with Pattern LHS and RHS
```

---

## Pending Phases

### Phase 5: FFT/NTT

- [ ] Add `Pattern.cast` for modular constants
- [ ] Support non-literal exponents
- [ ] Polynomial evaluation in finite fields
- [ ] FFT as operation composition

### Phase 6+: FRI and Production

- [ ] Merkle commitments
- [ ] Folding rounds
- [ ] Rust code generation
- [ ] Production engineering

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
│  Level 1: Arithmetic Expressions  ◄──── WE ARE HERE (pow ready)       │
│           ├── Generic AST with pow                                     │
│           ├── E-graph saturation                                       │
│           └── Code generation                                          │
│                                                                        │
└────────────────────────────────────────────────────────────────────────┘
```

---

## Complexity Estimate

```
                        Complexity     Status           Dependencies
                        ──────────     ──────           ────────────
Phase 1: Toy Model      ████░░░░░░     ✅ COMPLETED     None
Phase 1.5: Verification ████░░░░░░     ✅ COMPLETED     Toy Model
Phase 1.75: Pre-E-graph ████░░░░░░     ✅ COMPLETED     Verification
Phase 2: E-graph        █████░░░░░     ✅ COMPLETED     Pre-E-graph
Phase 3: Mathlib Ext    █████░░░░░     ✅ COMPLETED     E-graph
Phase 4: Power+ZMod     ██████░░░░     ✅ COMPLETED     Mathlib Ext
Phase 5: FFT            ███████░░░     🔜 Planned       Power+ZMod
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
*Last update: January 23, 2026 - Phase 4 (Power + ZMod) completed*
