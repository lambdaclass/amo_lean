# Insights: Verified C Codegen Pipeline (MixedExpr → Trust-Lean → MicroC → C)

**Fecha**: 2026-03-17
**Dominio**: lean4
**Estado**: upgrade (AMO-Lean v3.2.0 → v3.2.4)
**Profundidad**: deep (4 agentes, skip-online)

---

## 1. Trust-Lean MicroC Pipeline (from Agent 1)

### Exact Constructor Mapping

**Stmt (12)**: assign, store, load, seq, ite, while, for_, call, skip, break_, continue_, return_
**MicroCStmt (11)**: same minus for_ (desugared to seq + while)
**BinOp (12)**: add, sub, mul, eqOp, ltOp, land, lor, band, bor, bxor, bshl, bshr
**UnaryOp (4)**: neg, lnot, widen32to64, trunc64to32
**LowLevelExpr (6)**: litInt, litBool, varRef, binOp, unaryOp, powCall

### Forward Simulation Theorem

`stmtToMicroC_correct`:
- Preconditions: microCBridge (env agree), VarNameInjective, oc ≠ outOfFuel, WellFormedArrayBases
- Postcondition: ∃ mcEnv', evalMicroC produces same outcome + bridged env
- Proof: structural induction on 12 Stmt cases

### Plonky3 Field Bridge Pattern (Mersenne31)

```lean
def reduce_mersenne31_prog : MicroCStmt :=
  .seq (.assign "lo" (.binOp .band (.varRef "x") (.litInt mask31)))
  (.seq (.assign "hi" (.binOp .bshr (.varRef "x") (.litInt 31)))
  (.seq (.assign "sum" (.binOp .add (.varRef "lo") (.varRef "hi")))
  (.ite (.binOp .ltOp (.litInt (P - 1)) (.varRef "sum"))
    (.assign "sum" (.binOp .sub (.varRef "sum") (.litInt P))) .skip)
  (.assign "result" (.varRef "sum"))))
```

Verified via `evalMicroC_uint32` + `native_decide` on concrete inputs.

---

## 2. MixedExpr → LowLevelExpr Exact Mapping (from Agent 4)

| MixedExpr | LowLevelExpr | Status |
|-----------|-------------|--------|
| constE n | litInt (constVal n) | OK (needs env lookup) |
| witnessE n | varRef (.temp n) | OK (name mangle) |
| pubInputE n | varRef (.temp (n+offset)) | OK (name mangle) |
| addE a b | binOp .add (toLL a) (toLL b) | DIRECT |
| mulE a b | binOp .mul (toLL a) (toLL b) | DIRECT |
| negE a | unaryOp .neg (toLL a) | DIVERGENT (Nat→0, Int→true neg) |
| smulE n a | binOp .mul (litInt n) (toLL a) | DIRECT |
| shiftLeftE a n | binOp .bshl (toLL a) (litInt n) | DIRECT |
| shiftRightE a n | binOp .bshr (toLL a) (litInt n) | DIRECT |
| bitAndE a b | binOp .band (toLL a) (toLL b) | DIRECT |
| bitXorE a b | binOp .bxor (toLL a) (toLL b) | DIRECT |
| bitOrE a b | binOp .bor (toLL a) (toLL b) | DIRECT |
| constMaskE n | litInt (2^n - 1) | DIRECT |

**11/13 direct**, 1 needs constant env, 1 semantic divergence (negE — documented as Nat placeholder).

---

## 3. TrustHash Dual Representation (from Agent 2)

### Pattern: chi5 (BitVec 5) ↔ chiNat (Nat)

- BitVec version uses &&&, ^^^, >>>, |||, ~~~ — hardware-like
- Nat version uses Nat.land, Nat.xor, subtraction — proof-friendly
- Bridge via bit extraction: chi5_equiv proved by native_decide on 2^5 cases
- **Transferable**: Same pattern for evalMixedOp (Nat) ↔ evalMixedOpBV (BitVec)

### CipherBridge: Concrete ↔ Formal

- `aes_exec_uses_certified_sbox`: native_decide validates concrete parameters
- Pattern: formal framework(specific_params) = specific_definition (rfl/native_decide)
- **Transferable**: Validate C code uses same constants as formal spec

---

## 4. Key Lessons (from Agent 2)

| ID | Lesson | Application |
|----|--------|-------------|
| L-512 | Three-tier bridge (shell/core/bridge) | MicroC eval = shell, Stmt eval = core, bridge theorem = bridge |
| L-543 | Generic-to-specific bridge agreement | CostModel framework agrees with ARM-specific instance |
| L-566 | Bool-to-Prop with native_decide | Validate circuit properties computationally |
| L-336 | Type-first isomorphism design | Define MixedExpr→LowLevelExpr as injection FIRST, prove bridge SECOND |
| L-578 | MicroC fuel simpler (no for_) | Desugared AST simplifies termination proofs |

---

## 5. Unsigned Wrapping (from Agent 4)

Trust-Lean's `wrapWidth w x = x % 2^w`:
- Non-negative, bounded, idempotent (all proved)
- Compositional: wrapWidth_add, wrapWidth_mul (modular arithmetic homomorphism)
- Evaluators: evalMicroC_uint32, evalMicroC_uint64

**Bridge**: MixedExpr.eval (Nat) ↔ wrapUInt64(evalExpr (Int)) via Nat ↪ Int cast.

---

## 6. Enhanced Cost Model Fields Needed

**Existing** (8 fields): mul32, mul64, add, sub, shift, bitAnd, bitXor, bitOr

**Proposed additions** (for register pressure + SIMD):

| Field | Type | Purpose |
|-------|------|---------|
| availableGPR | Nat | ARM=31, RISC-V=31, x86=16 |
| spillCost | Nat | L1 latency: ~4 cycles |
| simdWidth | Nat | AVX2=8, NEON=4, none=1 |
| simdMulCost | Nat | Cost of SIMD multiply |

**Cost formula**: totalCost = Σ mixedOpCost + max(0, temps - GPR) × spillCost - simdBonus

---

## 7. Synthesis: End-to-End Pipeline

```
synthesizeReduction(p, hw)          -- AMO-Lean Fase 22
    ↓ SynthesisResult.step          -- ReductionStep with soundness
    ↓ toTrustLeanExpr               -- NEW: MixedExpr → LowLevelExpr
Stmt.assign "result" (expr)         -- Trust-Lean Core IR
    ↓ stmtToMicroC                  -- Trust-Lean (existing, verified)
MicroCStmt                          -- Trust-Lean MicroC AST
    ↓ microCToString                -- Trust-Lean (existing, roundtrip)
C code string                       -- Emitted, verified
    ↓ evalMicroC_uint32/64 + native_decide
Correctness validated               -- Concrete test vectors
```

**New work**: toTrustLeanExpr (~200 LOC) + soundness proof (~150 LOC) + KoalaBear/Goldilocks bridges (~150 LOC) + enhanced cost model (~300 LOC) + BitVec bridge (~500 LOC for C.1)
