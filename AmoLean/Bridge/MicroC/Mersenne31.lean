/-
  AMO-Lean v2.8.0 — Mersenne31 MicroC Programs
  N19.1 (FUNDACIONAL): Plonky3's Mersenne31 field operations as MicroC programs.

  Each def is a MicroC program mirroring the Plonky3 Rust implementation.
  Smoke tests verify correct computation via evalMicroC_uint64.

  Reference: Plonky3 mersenne-31 crate
  - mersenne_31.rs: from_u62, mul, neg
  - monty-31 Add/Sub impls (semantic level)
-/

import TrustLean.MicroC.UnsignedEval
import AmoLean.Field.Plonky3.Mersenne31TV

set_option autoImplicit false

namespace AmoLean.Bridge.MicroC.Mersenne31

open TrustLean

/-! ## Constants -/

/-- Mersenne31 prime: 2^31 - 1. -/
def P : Int := 2147483647

/-- Bitmask for low 31 bits: 0x7FFFFFFF = 2^31 - 1. -/
def MASK31 : Int := 0x7FFFFFFF

/-! ## reduce_prog — Mersenne-specific reduction (from_u62)

Plonky3 Rust (mersenne_31.rs:540-545):
```rust
fn from_u62(input: u64) -> Mersenne31 {
    let input_lo = (input & ((1 << 31) - 1)) as u32;
    let input_high = (input >> 31) as u32;
    Mersenne31::new_reduced(input_lo) + Mersenne31::new_reduced(input_high)
}
```

Input: env("val") = x (should be < 2^62)
Output: env("result") = x % P

Algorithm: lo = val & 0x7FFFFFFF; hi = val >> 31; sum = lo + hi;
           if sum >= P then sum = sum - P; result = sum
-/

/-- Mersenne31 from_u62: reduce a value < 2^62 modulo P = 2^31 - 1.
    Uses the identity 2^31 ≡ 1 (mod P) to split into two 31-bit halves. -/
def reduce_prog : MicroCStmt :=
  .seq (.assign "lo" (.binOp .band (.varRef "val") (.litInt MASK31)))
  (.seq (.assign "hi" (.binOp .bshr (.varRef "val") (.litInt 31)))
  (.seq (.assign "sum" (.binOp .add (.varRef "lo") (.varRef "hi")))
  (.seq (.ite (.binOp .ltOp (.litInt (P - 1)) (.varRef "sum"))
              (.assign "sum" (.binOp .sub (.varRef "sum") (.litInt P)))
              .skip)
        (.assign "result" (.varRef "sum")))))

/-! ## add_prog — Mersenne31 addition

Plonky3 semantic: sum = a + b; if sum >= P then sum - P else sum.
(Rust uses i32 overflow trick, but the math is identical.)

Input: env("a"), env("b") — field elements in [0, P)
Output: env("result") = (a + b) % P
-/

/-- Mersenne31 addition: conditional subtraction of P. -/
def add_prog : MicroCStmt :=
  .seq (.assign "sum" (.binOp .add (.varRef "a") (.varRef "b")))
  (.seq (.ite (.binOp .ltOp (.litInt (P - 1)) (.varRef "sum"))
              (.assign "sum" (.binOp .sub (.varRef "sum") (.litInt P)))
              .skip)
        (.assign "result" (.varRef "sum")))

/-! ## sub_prog — Mersenne31 subtraction

Plonky3 semantic: if a >= b then a - b else a + P - b.
(Rust uses u32 borrow + mask trick, but the math is identical.)

Input: env("a"), env("b") — field elements in [0, P)
Output: env("result") = (a - b) % P  (= a - b + P when a < b)
-/

/-- Mersenne31 subtraction: borrow correction by adding P. -/
def sub_prog : MicroCStmt :=
  .ite (.binOp .ltOp (.varRef "a") (.varRef "b"))
    -- a < b: result = a + P - b
    (.assign "result" (.binOp .sub (.binOp .add (.varRef "a") (.litInt P)) (.varRef "b")))
    -- a >= b: result = a - b
    (.assign "result" (.binOp .sub (.varRef "a") (.varRef "b")))

/-! ## neg_prog — Mersenne31 negation

Plonky3 Rust: `Self::new_reduced(Self::ORDER_U32 - self.value)`

Input: env("a") — field element in [0, P)
Output: env("result") = P - a (with special case: neg(0) = 0)
-/

/-- Mersenne31 negation: P - a, with conditional for zero. -/
def neg_prog : MicroCStmt :=
  .ite (.binOp .eqOp (.varRef "a") (.litInt 0))
    (.assign "result" (.litInt 0))
    (.assign "result" (.binOp .sub (.litInt P) (.varRef "a")))

/-! ## mul_prog — Mersenne31 multiplication

Plonky3 Rust:
```rust
fn mul(self, rhs: Self) -> Self {
    let prod = u64::from(self.value) * u64::from(rhs.value);
    from_u62(prod)
}
```

Input: env("a"), env("b") — field elements in [0, P)
Output: env("result") = (a * b) % P

Algorithm: prod = a * b; then reduce via from_u62 (inline).
-/

/-- Mersenne31 multiplication: product then from_u62 reduction. -/
def mul_prog : MicroCStmt :=
  .seq (.assign "val" (.binOp .mul (.varRef "a") (.varRef "b")))
  -- Inline from_u62 reduction on "val"
  (.seq (.assign "lo" (.binOp .band (.varRef "val") (.litInt MASK31)))
  (.seq (.assign "hi" (.binOp .bshr (.varRef "val") (.litInt 31)))
  (.seq (.assign "sum" (.binOp .add (.varRef "lo") (.varRef "hi")))
  (.seq (.ite (.binOp .ltOp (.litInt (P - 1)) (.varRef "sum"))
              (.assign "sum" (.binOp .sub (.varRef "sum") (.litInt P)))
              .skip)
        (.assign "result" (.varRef "sum"))))))

/-! ## Smoke Tests -/

/-- Helper: build environment from named int pairs. -/
private def mkEnv (bindings : List (String × Int)) : MicroCEnv :=
  bindings.foldl (fun env (k, v) => env.update k (.int v)) MicroCEnv.default

/-- Helper: extract int result from evaluation. -/
private def getResult (env : MicroCEnv) : Option Int :=
  match env "result" with
  | .int n => some n
  | _ => none

-- reduce: 2^31 + 42 → lo = 42, hi = 1, sum = 43, result = 43
#eval do
  let env := mkEnv [("val", 2^31 + 42)]
  match evalMicroC_uint64 10 env reduce_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 43 then IO.println "reduce(2^31+42) = 43 OK"
    else IO.println s!"reduce FAIL: got {r}"
  | _ => IO.println "reduce FAIL: eval error"

-- reduce: 0 → 0
#eval do
  let env := mkEnv [("val", 0)]
  match evalMicroC_uint64 10 env reduce_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 0 then IO.println "reduce(0) = 0 OK"
    else IO.println s!"reduce(0) FAIL: got {r}"
  | _ => IO.println "reduce(0) FAIL: eval error"

-- reduce: P-1 → P-1 (no subtraction needed, sum = P-1 + 0 = P-1 < P)
#eval do
  let env := mkEnv [("val", 2147483646)]
  match evalMicroC_uint64 10 env reduce_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 2147483646 then IO.println "reduce(P-1) = P-1 OK"
    else IO.println s!"reduce(P-1) FAIL: got {r}"
  | _ => IO.println "reduce(P-1) FAIL: eval error"

-- reduce: P → 0 (lo = P, hi = 0, sum = P >= P, result = 0)
#eval do
  let env := mkEnv [("val", 2147483647)]
  match evalMicroC_uint64 10 env reduce_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 0 then IO.println "reduce(P) = 0 OK"
    else IO.println s!"reduce(P) FAIL: got {r}"
  | _ => IO.println "reduce(P) FAIL: eval error"

-- add: 100 + 200 = 300
#eval do
  let env := mkEnv [("a", 100), ("b", 200)]
  match evalMicroC_uint64 10 env add_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 300 then IO.println "add(100,200) = 300 OK"
    else IO.println s!"add FAIL: got {r}"
  | _ => IO.println "add FAIL: eval error"

-- add: (P-1) + 1 = 0 (wraps around)
#eval do
  let env := mkEnv [("a", 2147483646), ("b", 1)]
  match evalMicroC_uint64 10 env add_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 0 then IO.println "add(P-1,1) = 0 OK"
    else IO.println s!"add(P-1,1) FAIL: got {r}"
  | _ => IO.println "add(P-1,1) FAIL: eval error"

-- sub: 200 - 100 = 100
#eval do
  let env := mkEnv [("a", 200), ("b", 100)]
  match evalMicroC_uint64 10 env sub_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 100 then IO.println "sub(200,100) = 100 OK"
    else IO.println s!"sub FAIL: got {r}"
  | _ => IO.println "sub FAIL: eval error"

-- sub: 0 - 1 = P-1
#eval do
  let env := mkEnv [("a", 0), ("b", 1)]
  match evalMicroC_uint64 10 env sub_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 2147483646 then IO.println "sub(0,1) = P-1 OK"
    else IO.println s!"sub(0,1) FAIL: got {r}"
  | _ => IO.println "sub(0,1) FAIL: eval error"

-- neg: neg(0) = 0
#eval do
  let env := mkEnv [("a", 0)]
  match evalMicroC_uint64 10 env neg_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 0 then IO.println "neg(0) = 0 OK"
    else IO.println s!"neg(0) FAIL: got {r}"
  | _ => IO.println "neg(0) FAIL: eval error"

-- neg: neg(1) = P-1
#eval do
  let env := mkEnv [("a", 1)]
  match evalMicroC_uint64 10 env neg_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 2147483646 then IO.println "neg(1) = P-1 OK"
    else IO.println s!"neg(1) FAIL: got {r}"
  | _ => IO.println "neg(1) FAIL: eval error"

-- mul: 3 * 7 = 21
#eval do
  let env := mkEnv [("a", 3), ("b", 7)]
  match evalMicroC_uint64 10 env mul_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 21 then IO.println "mul(3,7) = 21 OK"
    else IO.println s!"mul FAIL: got {r}"
  | _ => IO.println "mul FAIL: eval error"

-- mul: (P-1) * 2 = P-2 (since (P-1)*2 = 2P-2, mod P = P-2)
#eval do
  let env := mkEnv [("a", 2147483646), ("b", 2)]
  match evalMicroC_uint64 10 env mul_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 2147483645 then IO.println "mul(P-1,2) = P-2 OK"
    else IO.println s!"mul(P-1,2) FAIL: got {r}"
  | _ => IO.println "mul(P-1,2) FAIL: eval error"

end AmoLean.Bridge.MicroC.Mersenne31
