/-
  AMO-Lean — KoalaBear MicroC Programs (Fase 29)
  KoalaBear field operations as MicroC programs.
  P = 2^31 - 2^24 + 1 = 2130706433 (Plonky3 monty-31 crate).
  Montgomery form with R = 2^32.

  Each def is a MicroC program mirroring the Plonky3 Rust implementation.
  Smoke tests verify correct computation via evalMicroC.

  Reference: Plonky3 monty-31 crate
  - utils.rs: add, sub, monty_reduce
  - KoalaBear: P = 2130706433 = 2^31 - 2^24 + 1

  0 sorry, 0 new axioms.
-/

import TrustLean.MicroC.Eval

set_option autoImplicit false

namespace AmoLean.Bridge.MicroC.KoalaBear

open TrustLean

/-! ## Constants -/

/-- KoalaBear prime: 2^31 - 2^24 + 1 = 2130706433. -/
def P : Int := 2130706433

/-- Montgomery MU_NEG: R - p^(-1) mod R = 2130706431.
    Used in the addition variant of Montgomery reduction. -/
def MU_NEG : Int := 2130706431

/-- Bitmask for low 32 bits: 0xFFFFFFFF = 2^32 - 1. -/
def MASK32 : Int := 0xFFFFFFFF

/-! ## add_prog — KoalaBear addition

Plonky3 Rust (monty-31/utils.rs:63-70):
```rust
let mut sum = lhs + rhs;
let (corr_sum, over) = sum.overflowing_sub(MP::PRIME);
if !over { sum = corr_sum; }
```

Semantic: sum = a + b; if sum >= P then sum - P else sum.

Input: env("a"), env("b") — field elements in [0, P)
Output: env("result") = (a + b) % P
-/

/-- KoalaBear addition: conditional subtraction of P. -/
def add_prog : MicroCStmt :=
  .seq (.assign "sum" (.binOp .add (.varRef "a") (.varRef "b")))
  (.seq (.ite (.binOp .ltOp (.litInt (P - 1)) (.varRef "sum"))
              (.assign "sum" (.binOp .sub (.varRef "sum") (.litInt P)))
              .skip)
        (.assign "result" (.varRef "sum")))

/-! ## sub_prog — KoalaBear subtraction

Plonky3 Rust (monty-31/utils.rs:81-86):
```rust
let (mut diff, over) = lhs.overflowing_sub(rhs);
let corr = if over { MP::PRIME } else { 0 };
diff = diff.wrapping_add(corr);
```

Semantic: if a >= b then a - b else a + P - b.

Input: env("a"), env("b") — field elements in [0, P)
Output: env("result") = (a - b) % P  (= a - b + P when a < b)
-/

/-- KoalaBear subtraction: borrow correction by adding P. -/
def sub_prog : MicroCStmt :=
  .ite (.binOp .ltOp (.varRef "a") (.varRef "b"))
    -- a < b: result = a + P - b
    (.assign "result" (.binOp .sub (.binOp .add (.varRef "a") (.litInt P)) (.varRef "b")))
    -- a >= b: result = a - b
    (.assign "result" (.binOp .sub (.varRef "a") (.varRef "b")))

/-! ## neg_prog — KoalaBear negation

Plonky3 Rust: `Self::new_reduced(Self::ORDER_U32 - self.value)`

Input: env("a") — field element in [0, P)
Output: env("result") = P - a (with special case: neg(0) = 0)
-/

/-- KoalaBear negation: P - a, with conditional for zero. -/
def neg_prog : MicroCStmt :=
  .ite (.binOp .eqOp (.varRef "a") (.litInt 0))
    (.assign "result" (.litInt 0))
    (.assign "result" (.binOp .sub (.litInt P) (.varRef "a")))

/-! ## monty_reduce_prog — Montgomery reduction (addition variant)

Uses the addition variant matching AmoLean/Field/Montgomery.lean:
  m = (x * MU_NEG) & 0xFFFFFFFF      — low 32 bits of x * MU_NEG
  s = x + m * P                       — always >= x, divisible by R = 2^32
  q = s >> 32                          — quotient in [0, 2P)
  if q >= P then q - P else q         — normalize to [0, P)

All intermediates fit in uint64: s < 2*R*P < 2^64.

Input: env("val") = x (should be < R * P)
Output: env("result") = monty_reduce(x), satisfying R * result ≡ x (mod P)
-/

/-- KoalaBear Montgomery reduction (addition variant). -/
def monty_reduce_prog : MicroCStmt :=
  -- m = (val * MU_NEG) & MASK32
  .seq (.assign "m" (.binOp .band
          (.binOp .mul (.varRef "val") (.litInt MU_NEG))
          (.litInt MASK32)))
  -- s = val + m * P
  (.seq (.assign "s" (.binOp .add (.varRef "val")
          (.binOp .mul (.varRef "m") (.litInt P))))
  -- q = s >> 32
  (.seq (.assign "q" (.binOp .bshr (.varRef "s") (.litInt 32)))
  -- if q >= P then q = q - P
  (.seq (.ite (.binOp .ltOp (.litInt (P - 1)) (.varRef "q"))
              (.assign "q" (.binOp .sub (.varRef "q") (.litInt P)))
              .skip)
        (.assign "result" (.varRef "q")))))

/-! ## mul_prog — KoalaBear Montgomery multiplication

Plonky3 Rust:
```rust
fn mul(self, rhs: Self) -> Self {
    monty_reduce(u64::from(self.value) * u64::from(rhs.value))
}
```

Input: env("a"), env("b") — field elements in Montgomery form, in [0, P)
Output: env("result") = monty_reduce(a * b)

Product (P-1)^2 < 2^62 < R*P, so the input to monty_reduce is valid.
-/

/-- KoalaBear Montgomery multiplication: product then monty_reduce. -/
def mul_prog : MicroCStmt :=
  .seq (.assign "val" (.binOp .mul (.varRef "a") (.varRef "b")))
  -- Inline monty_reduce on "val"
  (.seq (.assign "m" (.binOp .band
          (.binOp .mul (.varRef "val") (.litInt MU_NEG))
          (.litInt MASK32)))
  (.seq (.assign "s" (.binOp .add (.varRef "val")
          (.binOp .mul (.varRef "m") (.litInt P))))
  (.seq (.assign "q" (.binOp .bshr (.varRef "s") (.litInt 32)))
  (.seq (.ite (.binOp .ltOp (.litInt (P - 1)) (.varRef "q"))
              (.assign "q" (.binOp .sub (.varRef "q") (.litInt P)))
              .skip)
        (.assign "result" (.varRef "q"))))))

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
  let env := mkEnv [("a", 2130706432), ("b", 1)]
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
    if r == some 2130706432 then IO.println "sub(0,1) = P-1 OK"
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
    if r == some 2130706432 then IO.println "neg(1) = P-1 OK"
    else IO.println s!"neg(1) FAIL: got {r}"
  | _ => IO.println "neg(1) FAIL: eval error"

-- monty_reduce: monty_reduce(0) = 0
#eval do
  let env := mkEnv [("val", 0)]
  match evalMicroC 20 env monty_reduce_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 0 then IO.println "monty_reduce(0) = 0 OK"
    else IO.println s!"monty_reduce(0) FAIL: got {r}"
  | _ => IO.println "monty_reduce(0) FAIL: eval error"

-- monty_reduce: monty_reduce(42) = 1781137388
-- Verify: 1781137388 * 2^32 mod P = 42
#eval do
  let env := mkEnv [("val", 42)]
  match evalMicroC 20 env monty_reduce_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 1781137388 then IO.println "monty_reduce(42) = 1781137388 OK"
    else IO.println s!"monty_reduce(42) FAIL: got {r}"
  | _ => IO.println "monty_reduce(42) FAIL: eval error"

-- monty_reduce: monty_reduce(P) = 0
#eval do
  let env := mkEnv [("val", 2130706433)]
  match evalMicroC 20 env monty_reduce_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 0 then IO.println "monty_reduce(P) = 0 OK"
    else IO.println s!"monty_reduce(P) FAIL: got {r}"
  | _ => IO.println "monty_reduce(P) FAIL: eval error"

-- mul: 0 * 42 = 0
#eval do
  let env := mkEnv [("a", 0), ("b", 42)]
  match evalMicroC 20 env mul_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 0 then IO.println "mul(0,42) = 0 OK"
    else IO.println s!"mul(0,42) FAIL: got {r}"
  | _ => IO.println "mul(0,42) FAIL: eval error"

-- mul: 100 * 200 = monty_reduce(20000) = 1864358207
-- Verify: 1864358207 * 2^32 mod P = 20000
#eval do
  let env := mkEnv [("a", 100), ("b", 200)]
  match evalMicroC 20 env mul_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 1864358207 then IO.println "mul(100,200) = 1864358207 OK"
    else IO.println s!"mul(100,200) FAIL: got {r}"
  | _ => IO.println "mul(100,200) FAIL: eval error"

-- mul: (P-1) * (P-1) = monty_reduce((P-1)^2) = 1057030144
-- Verify: (P-1)^2 mod P = 1, so result * R mod P = 1
#eval do
  let env := mkEnv [("a", 2130706432), ("b", 2130706432)]
  match evalMicroC 20 env mul_prog with
  | some (.normal, env') =>
    let r := getResult env'
    if r == some 1057030144 then IO.println "mul(P-1,P-1) = 1057030144 OK"
    else IO.println s!"mul(P-1,P-1) FAIL: got {r}"
  | _ => IO.println "mul(P-1,P-1) FAIL: eval error"

end AmoLean.Bridge.MicroC.KoalaBear
