/-
  AMO-Lean — Goldilocks MicroC Programs (Fase 29, N29.4)

  Goldilocks field operations as MicroC programs.
  P = 2^64 - 2^32 + 1 = 18446744069414584321

  NOTE: Goldilocks elements EXCEED Int64Range (max ~9.2x10^18).
  These programs use the UNBOUNDED MicroC evaluator (`evalMicroC`).
  TrustLean's Int64 agreement theorem (`binOp_agreement`) does NOT apply.
  For production Goldilocks codegen, use `__uint128_t` accumulators or
  split-radix multiplication.

  IMPORTANT: TrustLean's `bshr` takes the shift amount modulo 64, so
  `bshr x 64 = x` (no-op). We use two-stage 32-bit shifts to achieve
  a 64-bit right shift: `bshr (bshr x 32) 32`.

  0 sorry, 0 new axioms.
-/

import TrustLean.MicroC.Eval

set_option autoImplicit false

namespace AmoLean.Bridge.MicroC.Goldilocks

open TrustLean

/-! ## Constants -/

/-- Goldilocks prime: 2^64 - 2^32 + 1 = 18446744069414584321. -/
def P : Int := 18446744069414584321

/-- Bitmask for low 32 bits: 0xFFFFFFFF = 2^32 - 1. -/
def MASK32 : Int := 0xFFFFFFFF

/-- Epsilon: 2^32 - 1. Since p = 2^64 - epsilon, we have 2^64 ≡ epsilon (mod p). -/
def EPSILON : Int := 0xFFFFFFFF

/-- Bitmask for low 64 bits: 2^64 - 1. -/
def MASK64 : Int := 18446744073709551615

/-! ## Helper: two-stage right shift by 64

TrustLean's `bshr` computes `Int.shiftRight a (b.toNat % 64)`, so
`bshr x 64` shifts by 0 (a no-op). We compose two 32-bit shifts instead:
`bshr (bshr x 32) 32` = `x >> 32 >> 32` = `x >> 64`.
-/

/-- Expression: right-shift by 64 via two 32-bit shifts. -/
private def shr64 (e : MicroCExpr) : MicroCExpr :=
  .binOp .bshr (.binOp .bshr e (.litInt 32)) (.litInt 32)

/-! ## add_prog — Goldilocks addition

Semantic: sum = a + b; if sum >= P then sum - P else sum.

Input: env("a"), env("b") — field elements in [0, P)
Output: env("result") = (a + b) % P

Since a, b < P < 2^64, sum < 2P, so one conditional subtraction suffices.
-/

/-- Goldilocks addition: conditional subtraction of P. -/
def add_prog : MicroCStmt :=
  .seq (.assign "sum" (.binOp .add (.varRef "a") (.varRef "b")))
  (.seq (.ite (.binOp .ltOp (.litInt (P - 1)) (.varRef "sum"))
              (.assign "sum" (.binOp .sub (.varRef "sum") (.litInt P)))
              .skip)
        (.assign "result" (.varRef "sum")))

/-! ## sub_prog — Goldilocks subtraction

Semantic: if a >= b then a - b else a + P - b.

Input: env("a"), env("b") — field elements in [0, P)
Output: env("result") = (a - b) % P  (= a - b + P when a < b)
-/

/-- Goldilocks subtraction: borrow correction by adding P. -/
def sub_prog : MicroCStmt :=
  .ite (.binOp .ltOp (.varRef "a") (.varRef "b"))
    -- a < b: result = a + P - b
    (.assign "result" (.binOp .sub (.binOp .add (.varRef "a") (.litInt P)) (.varRef "b")))
    -- a >= b: result = a - b
    (.assign "result" (.binOp .sub (.varRef "a") (.varRef "b")))

/-! ## neg_prog — Goldilocks negation

Input: env("a") — field element in [0, P)
Output: env("result") = P - a (with special case: neg(0) = 0)
-/

/-- Goldilocks negation: P - a, with conditional for zero. -/
def neg_prog : MicroCStmt :=
  .ite (.binOp .eqOp (.varRef "a") (.litInt 0))
    (.assign "result" (.litInt 0))
    (.assign "result" (.binOp .sub (.litInt P) (.varRef "a")))

/-! ## reduce_prog — Goldilocks reduction (conditional subtraction)

Reduces a value in [0, 2P) to [0, P) via a single conditional subtraction.
This is used for outputs of add/sub that may be in [0, 2P).

For full Solinas reduction from larger values (e.g., products), see
the inline reduction in `mul_prog`.

Input: env("val") — value in [0, 2P)
Output: env("result") = val % P
-/

/-- Goldilocks conditional reduction for values in [0, 2P). -/
def reduce_prog : MicroCStmt :=
  .ite (.binOp .ltOp (.litInt (P - 1)) (.varRef "val"))
    (.assign "result" (.binOp .sub (.varRef "val") (.litInt P)))
    (.assign "result" (.varRef "val"))

/-! ## mul_prog — Goldilocks multiplication (Solinas reduction)

Uses the identity 2^64 ≡ 2^32 - 1 (mod P) for reduction.
For a product up to (P-1)^2 < 2^128, two Solinas folds suffice:

  Fold 1: hi = product >> 64; lo = product & MASK64;
          t = lo + hi * EPSILON
  Fold 2: hi2 = t >> 64; lo2 = t & MASK64;
          t2 = lo2 + hi2 * EPSILON
  Normalize: if t2 >= P then t2 - P else t2

Correctness: After fold 1, t < 2^64 + P * EPSILON < 2^96.
After fold 2, t2 < 2^64 + 2^32 * EPSILON < 2^65.
One conditional subtraction then normalizes to [0, P).

NOTE: Since `bshr` takes shift amount mod 64, we use `shr64` (two
32-bit shifts) to achieve the 64-bit right shift.

Input: env("a"), env("b") — field elements in [0, P)
Output: env("result") = (a * b) % P
-/

/-- Goldilocks multiplication with inline Solinas reduction. -/
def mul_prog : MicroCStmt :=
  -- product = a * b (unbounded Int, can be up to (P-1)^2 ~ 2^128)
  .seq (.assign "product" (.binOp .mul (.varRef "a") (.varRef "b")))
  -- Fold 1: hi = product >> 64 (via two 32-bit shifts), lo = product & MASK64
  (.seq (.assign "hi" (shr64 (.varRef "product")))
  (.seq (.assign "lo" (.binOp .band (.varRef "product") (.litInt MASK64)))
  (.seq (.assign "t" (.binOp .add (.varRef "lo")
          (.binOp .mul (.varRef "hi") (.litInt EPSILON))))
  -- Fold 2: hi2 = t >> 64 (via two 32-bit shifts), lo2 = t & MASK64
  (.seq (.assign "hi2" (shr64 (.varRef "t")))
  (.seq (.assign "lo2" (.binOp .band (.varRef "t") (.litInt MASK64)))
  (.seq (.assign "t2" (.binOp .add (.varRef "lo2")
          (.binOp .mul (.varRef "hi2") (.litInt EPSILON))))
  -- Final normalize: if t2 >= P then t2 - P else t2
  (.ite (.binOp .ltOp (.litInt (P - 1)) (.varRef "t2"))
    (.assign "result" (.binOp .sub (.varRef "t2") (.litInt P)))
    (.assign "result" (.varRef "t2")))))))))

/-! ## Smoke Tests -/

/-- Helper: build environment from named int pairs. -/
private def mkEnv (bindings : List (String × Int)) : MicroCEnv :=
  bindings.foldl (fun env (k, v) => env.update k (.int v)) MicroCEnv.default

/-- Helper: extract int result from evaluation. -/
private def getResult (env : MicroCEnv) : Option Int :=
  match env "result" with
  | .int n => some n
  | _ => none

-- add: 100 + 200 = 300
#eval do
  let env := mkEnv [("a", 100), ("b", 200)]
  match evalMicroC 10 env add_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 300 then IO.println "add(100,200) = 300 OK"
    else IO.println s!"add FAIL: got {r}"
  | _ => IO.println "add FAIL: eval error"

-- add: (P-1) + 1 = 0 (wraps around)
#eval do
  let env := mkEnv [("a", 18446744069414584320), ("b", 1)]
  match evalMicroC 10 env add_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 0 then IO.println "add(P-1,1) = 0 OK"
    else IO.println s!"add(P-1,1) FAIL: got {r}"
  | _ => IO.println "add(P-1,1) FAIL: eval error"

-- sub: 200 - 100 = 100
#eval do
  let env := mkEnv [("a", 200), ("b", 100)]
  match evalMicroC 10 env sub_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 100 then IO.println "sub(200,100) = 100 OK"
    else IO.println s!"sub FAIL: got {r}"
  | _ => IO.println "sub FAIL: eval error"

-- sub: 0 - 1 = P-1
#eval do
  let env := mkEnv [("a", 0), ("b", 1)]
  match evalMicroC 10 env sub_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 18446744069414584320 then IO.println "sub(0,1) = P-1 OK"
    else IO.println s!"sub(0,1) FAIL: got {r}"
  | _ => IO.println "sub(0,1) FAIL: eval error"

-- neg: neg(0) = 0
#eval do
  let env := mkEnv [("a", 0)]
  match evalMicroC 10 env neg_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 0 then IO.println "neg(0) = 0 OK"
    else IO.println s!"neg(0) FAIL: got {r}"
  | _ => IO.println "neg(0) FAIL: eval error"

-- neg: neg(1) = P-1
#eval do
  let env := mkEnv [("a", 1)]
  match evalMicroC 10 env neg_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 18446744069414584320 then IO.println "neg(1) = P-1 OK"
    else IO.println s!"neg(1) FAIL: got {r}"
  | _ => IO.println "neg(1) FAIL: eval error"

-- reduce: reduce(0) = 0
#eval do
  let env := mkEnv [("val", 0)]
  match evalMicroC 10 env reduce_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 0 then IO.println "reduce(0) = 0 OK"
    else IO.println s!"reduce(0) FAIL: got {r}"
  | _ => IO.println "reduce(0) FAIL: eval error"

-- reduce: reduce(P) = 0 (P >= P, so result = P - P = 0)
#eval do
  let env := mkEnv [("val", 18446744069414584321)]
  match evalMicroC 10 env reduce_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 0 then IO.println "reduce(P) = 0 OK"
    else IO.println s!"reduce(P) FAIL: got {r}"
  | _ => IO.println "reduce(P) FAIL: eval error"

-- reduce: reduce(P-1) = P-1 (P-1 < P, no subtraction)
#eval do
  let env := mkEnv [("val", 18446744069414584320)]
  match evalMicroC 10 env reduce_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 18446744069414584320 then IO.println "reduce(P-1) = P-1 OK"
    else IO.println s!"reduce(P-1) FAIL: got {r}"
  | _ => IO.println "reduce(P-1) FAIL: eval error"

-- mul: 3 * 7 = 21
#eval do
  let env := mkEnv [("a", 3), ("b", 7)]
  match evalMicroC 20 env mul_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 21 then IO.println "mul(3,7) = 21 OK"
    else IO.println s!"mul FAIL: got {r}"
  | _ => IO.println "mul FAIL: eval error"

-- mul: 100 * 200 = 20000
#eval do
  let env := mkEnv [("a", 100), ("b", 200)]
  match evalMicroC 20 env mul_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 20000 then IO.println "mul(100,200) = 20000 OK"
    else IO.println s!"mul(100,200) FAIL: got {r}"
  | _ => IO.println "mul(100,200) FAIL: eval error"

-- mul: (P-1) * 2 = P-2 (since (P-1)*2 mod P = P-2)
#eval do
  let env := mkEnv [("a", 18446744069414584320), ("b", 2)]
  match evalMicroC 20 env mul_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 18446744069414584319 then IO.println "mul(P-1,2) = P-2 OK"
    else IO.println s!"mul(P-1,2) FAIL: got {r}"
  | _ => IO.println "mul(P-1,2) FAIL: eval error"

-- mul: (P-1) * (P-1) = 1 (since (P-1)^2 mod P = 1)
#eval do
  let env := mkEnv [("a", 18446744069414584320), ("b", 18446744069414584320)]
  match evalMicroC 20 env mul_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 1 then IO.println "mul(P-1,P-1) = 1 OK"
    else IO.println s!"mul(P-1,P-1) FAIL: got {r}"
  | _ => IO.println "mul(P-1,P-1) FAIL: eval error"

-- mul: 0 * 42 = 0
#eval do
  let env := mkEnv [("a", 0), ("b", 42)]
  match evalMicroC 20 env mul_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 0 then IO.println "mul(0,42) = 0 OK"
    else IO.println s!"mul(0,42) FAIL: got {r}"
  | _ => IO.println "mul(0,42) FAIL: eval error"

end AmoLean.Bridge.MicroC.Goldilocks
