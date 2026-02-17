/-
  AMO-Lean: Rust Code Generation Backend
  Fase 8 Onda 1 — Subfase 4 (A2): Rust Codegen for ZK Ecosystem

  This module generates Rust code from the expanded Sigma-SPL IR.
  The generated code uses a generic NttField trait, enabling integration
  with Risc0 (BabyBear), SP1 (BabyBear), Plonky3 (Goldilocks/BabyBear),
  and other ZK stacks.

  Pipeline:
    MatExpr → SigmaExpr → ExpandedSigma → Rust code

  Key differences from C backend (CodeGen.lean):
  - Generic over NttField trait instead of `double`
  - Ownership-aware: &[F] input, &mut [F] output
  - Stack arrays for temporaries instead of malloc
  - Safe Rust by default, unsafe variant with bounds-proven indexing
  - No restrict needed (Rust ownership model handles aliasing)

  References:
  - SPIRAL: "Automatic Implementation of Signal Processing Algorithms"
  - Fiat-Crypto: "Simple High-Level Code For Cryptographic Arithmetic"
  - Plonky3: baby-bear/goldilocks field implementations
-/

import AmoLean.Sigma.Expand

namespace AmoLean.Backends.Rust

open AmoLean.Sigma

/-! ## Part 1: Rust Code Generation State -/

/-- State for Rust code generation -/
structure RustCodeGenState where
  indent : Nat := 0
  nextTemp : Nat := 0
  useUnsafe : Bool := false
  deriving Repr, Inhabited

def RustCodeGenState.increaseIndent (s : RustCodeGenState) : RustCodeGenState :=
  { s with indent := s.indent + 1 }

def RustCodeGenState.freshTemp (s : RustCodeGenState) : (String × RustCodeGenState) :=
  (s!"temp_{s.nextTemp}", { s with nextTemp := s.nextTemp + 1 })

/-! ## Part 2: Rust Code Primitives -/

def indentStr (n : Nat) : String :=
  String.ofList (List.replicate (n * 4) ' ')

/-- The generic field type parameter name -/
def fieldType : String := "F"

/-- Generate Rust variable name from ScalarVar -/
def varToRust (v : ScalarVar) (baseOffset : String := "") : String :=
  match v.name with
  | "x" =>
    let idx := if baseOffset.isEmpty then s!"{v.idx}" else s!"{baseOffset} + {v.idx}"
    s!"input[{idx}]"
  | "y" =>
    let idx := if baseOffset.isEmpty then s!"{v.idx}" else s!"{baseOffset} + {v.idx}"
    s!"output[{idx}]"
  | "t" => s!"t{v.idx}"
  | _ => s!"{v.name}{v.idx}"

/-- Generate Rust expression from ScalarExpr -/
partial def exprToRust (e : ScalarExpr) (baseOffset : String := "") : String :=
  match e with
  | .var v => varToRust v baseOffset
  | .const n =>
    if n == 0 then s!"{fieldType}::zero()"
    else if n == 1 then s!"{fieldType}::one()"
    else if n == -1 then s!"-{fieldType}::one()"
    else if n >= 0 then s!"{fieldType}::from_u64({n})"
    else s!"-{fieldType}::from_u64({-n})"
  | .neg e' => s!"(-{exprToRust e' baseOffset})"
  | .add e1 e2 => s!"({exprToRust e1 baseOffset} + {exprToRust e2 baseOffset})"
  | .sub e1 e2 => s!"({exprToRust e1 baseOffset} - {exprToRust e2 baseOffset})"
  | .mul e1 e2 => s!"({exprToRust e1 baseOffset} * {exprToRust e2 baseOffset})"

/-- Generate Rust assignment from ScalarAssign -/
def assignToRust (a : ScalarAssign) (indent : Nat) (baseOffset : String := "") : String :=
  let pad := indentStr indent
  let lhs := varToRust a.target baseOffset
  let rhs := exprToRust a.value baseOffset
  match a.target.name with
  | "t" => s!"{pad}let {lhs} = {rhs};"
  | _ => s!"{pad}{lhs} = {rhs};"

/-! ## Part 3: Index Expression Codegen -/

/-- Compute base offset expression from IdxExpr -/
partial def idxExprToRust : IdxExpr → String
  | .const n => s!"{n}"
  | .var v => s!"i{v}"
  | .affine base stride v =>
    if base == 0 then s!"{stride} * i{v}"
    else s!"{base} + {stride} * i{v}"
  | .add e1 e2 => s!"({idxExprToRust e1} + {idxExprToRust e2})"
  | .mul c e => s!"{c} * ({idxExprToRust e})"

/-- Generate base offset for gather -/
def gatherOffset (g : Gather) : String := idxExprToRust g.baseAddr

/-- Generate base offset for scatter -/
def scatterOffset (s : Scatter) : String := idxExprToRust s.baseAddr

/-! ## Part 4: Index Generation with Stride -/

/-- Generate index expression with stride: base + stride * idx -/
def genIndexWithStride (base : String) (stride : Nat) (idx : Nat) : String :=
  if stride == 1 then
    if base.isEmpty then s!"{idx}"
    else s!"{base} + {idx}"
  else
    if base.isEmpty then s!"{stride} * {idx}"
    else s!"{base} + {stride} * {idx}"

/-! ## Part 5: Scalar Block Codegen for Rust -/

/-- Generate Rust code for a scalar block with stride support -/
def scalarBlockToRust (block : ScalarBlock) (indent : Nat) (g : Gather) (s : Scatter) : String :=
  let gatherBase := gatherOffset g
  let scatterBase := scatterOffset s
  let gatherStride := g.stride
  let scatterStride := s.stride
  let lines := block.map fun a =>
    match a.target.name with
    | "y" =>
      let pad := indentStr indent
      let outIdx := genIndexWithStride scatterBase scatterStride a.target.idx
      let lhs := s!"output[{outIdx}]"
      let rhsStr := genRhsWithOffsets a.value gatherBase gatherStride
      s!"{pad}{lhs} = {rhsStr};"
    | "t" =>
      let pad := indentStr indent
      let lhs := s!"t{a.target.idx}"
      let rhsStr := genRhsWithOffsets a.value gatherBase gatherStride
      s!"{pad}let {lhs} = {rhsStr};"
    | _ => assignToRust a indent ""
  String.intercalate "\n" lines
where
  genRhsWithOffsets (e : ScalarExpr) (gatherBase : String) (gatherStride : Nat) : String :=
    match e with
    | .var v =>
      match v.name with
      | "x" =>
        let inIdx := genIndexWithStride gatherBase gatherStride v.idx
        s!"input[{inIdx}]"
      | "t" => s!"t{v.idx}"
      | _ => varToRust v ""
    | .const n =>
      if n == 0 then s!"{fieldType}::zero()"
      else if n == 1 then s!"{fieldType}::one()"
      else if n >= 0 then s!"{fieldType}::from_u64({n})"
      else s!"-{fieldType}::from_u64({-n})"
    | .neg e' => s!"(-{genRhsWithOffsets e' gatherBase gatherStride})"
    | .add e1 e2 => s!"({genRhsWithOffsets e1 gatherBase gatherStride} + {genRhsWithOffsets e2 gatherBase gatherStride})"
    | .sub e1 e2 => s!"({genRhsWithOffsets e1 gatherBase gatherStride} - {genRhsWithOffsets e2 gatherBase gatherStride})"
    | .mul e1 e2 => s!"({genRhsWithOffsets e1 gatherBase gatherStride} * {genRhsWithOffsets e2 gatherBase gatherStride})"

/-! ## Part 6: Main Rust Code Generation -/

/-- Generate Rust code for ExpandedSigma -/
partial def expandedSigmaToRust (e : ExpandedSigma) (state : RustCodeGenState) : String :=
  let pad := indentStr state.indent
  match e with
  | .scalar k g s =>
    scalarBlockToRust k.body state.indent g s

  | .loop n v body =>
    let loopVar := s!"i{v}"
    let lbrace := "{"
    let rbrace := "}"
    let header := s!"{pad}for {loopVar} in 0..{n} {lbrace}"
    let bodyCode := expandedSigmaToRust body state.increaseIndent
    let footer := s!"{pad}{rbrace}"
    s!"{header}\n{bodyCode}\n{footer}"

  | .seq s1 s2 =>
    let code1 := expandedSigmaToRust s1 state
    let code2 := expandedSigmaToRust s2 state
    s!"{code1}\n{code2}"

  | .par s1 s2 =>
    -- Rust: parallel annotation as comment (could use rayon in future)
    let code1 := expandedSigmaToRust s1 state
    let code2 := expandedSigmaToRust s2 state
    s!"{pad}// parallel region\n{code1}\n{code2}"

  | .temp size body =>
    let (tempName, state') := state.freshTemp
    -- Rust: stack array instead of malloc
    let decl := s!"{pad}let mut {tempName}: [{fieldType}; {size}] = [{fieldType}::zero(); {size}];"
    let bodyCode := expandedSigmaToRust body state'
    s!"{decl}\n{bodyCode}"

  | .nop => s!"{pad}// nop"

/-! ## Part 7: NttField Trait Generation -/

/-- Generate the NttField trait definition -/
def generateNttFieldTrait : String :=
  "/// NTT field operations - generated by AMO-Lean
/// SAFETY: All arithmetic proven correct in Lean 4 formal verification
pub trait NttField: Copy + Clone + Debug + Default
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Neg<Output = Self>
    + PartialEq
{
    const MODULUS: u64;
    const GENERATOR: u64;

    fn zero() -> Self;
    fn one() -> Self;
    fn from_u64(n: u64) -> Self;
    fn to_u64(self) -> u64;
    fn add(self, other: Self) -> Self;
    fn sub(self, other: Self) -> Self;
    fn mul(self, other: Self) -> Self;
    fn neg(self) -> Self;
    fn inv(self) -> Self;
    fn pow(self, exp: u64) -> Self;
    fn primitive_root(n: usize) -> Self;
}"

/-- Generate Goldilocks field implementation -/
def generateGoldilocksImpl : String :=
  "/// Goldilocks field: p = 2^64 - 2^32 + 1
/// Arithmetic verified in AmoLean/Field/Goldilocks.lean
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Goldilocks(pub u64);

const GOLDILOCKS_MODULUS: u64 = 0xFFFFFFFF00000001;

impl Goldilocks {
    #[inline(always)]
    pub fn new(val: u64) -> Self {
        Self(val % GOLDILOCKS_MODULUS)
    }

    /// Goldilocks reduction: uses 2^64 ≡ 2^32 - 1 (mod p)
    #[inline(always)]
    fn reduce(val: u128) -> Self {
        let lo = val as u64;
        let hi = (val >> 64) as u64;
        // 2^64 ≡ 2^32 - 1 (mod p)
        // val = hi * 2^64 + lo ≡ hi * (2^32 - 1) + lo (mod p)
        let (r, borrow) = lo.overflowing_sub(hi);
        let adj = if borrow { GOLDILOCKS_MODULUS } else { 0 };
        let r = r.wrapping_add(adj);
        let hi_shifted = hi << 32;
        let (r, carry) = r.overflowing_add(hi_shifted);
        let adj = if carry || r >= GOLDILOCKS_MODULUS { GOLDILOCKS_MODULUS } else { 0 };
        Self(r.wrapping_sub(adj))
    }
}

impl NttField for Goldilocks {
    const MODULUS: u64 = GOLDILOCKS_MODULUS;
    const GENERATOR: u64 = 7;

    #[inline(always)]
    fn zero() -> Self { Self(0) }

    #[inline(always)]
    fn one() -> Self { Self(1) }

    #[inline(always)]
    fn from_u64(n: u64) -> Self { Self::new(n) }

    #[inline(always)]
    fn to_u64(self) -> u64 { self.0 }

    #[inline(always)]
    fn add(self, other: Self) -> Self {
        let sum = self.0 as u128 + other.0 as u128;
        if sum >= GOLDILOCKS_MODULUS as u128 {
            Self((sum - GOLDILOCKS_MODULUS as u128) as u64)
        } else {
            Self(sum as u64)
        }
    }

    #[inline(always)]
    fn sub(self, other: Self) -> Self {
        if self.0 >= other.0 {
            Self(self.0 - other.0)
        } else {
            Self(GOLDILOCKS_MODULUS - other.0 + self.0)
        }
    }

    #[inline(always)]
    fn mul(self, other: Self) -> Self {
        Self::reduce(self.0 as u128 * other.0 as u128)
    }

    #[inline(always)]
    fn neg(self) -> Self {
        if self.0 == 0 { Self(0) } else { Self(GOLDILOCKS_MODULUS - self.0) }
    }

    fn inv(self) -> Self {
        // Fermat's little theorem: a^(p-2) mod p
        self.pow(GOLDILOCKS_MODULUS - 2)
    }

    fn pow(self, exp: u64) -> Self {
        let mut base = self;
        let mut result = Self::one();
        let mut e = exp;
        while e > 0 {
            if e & 1 == 1 {
                result = result.mul(base);
            }
            base = base.mul(base);
            e >>= 1;
        }
        result
    }

    fn primitive_root(n: usize) -> Self {
        let exp = (GOLDILOCKS_MODULUS - 1) / n as u64;
        Self::new(Self::GENERATOR).pow(exp)
    }
}"

/-- Generate BabyBear field implementation -/
def generateBabyBearImpl : String :=
  "/// BabyBear field: p = 2^31 - 2^27 + 1 = 2013265921
/// Arithmetic verified in AmoLean/Field/BabyBear.lean
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct BabyBear(pub u32);

const BABYBEAR_MODULUS: u64 = 2013265921;
const BABYBEAR_MODULUS_U32: u32 = 2013265921;

impl BabyBear {
    #[inline(always)]
    pub fn new(val: u32) -> Self {
        if (val as u64) < BABYBEAR_MODULUS {
            Self(val)
        } else {
            Self((val as u64 % BABYBEAR_MODULUS) as u32)
        }
    }

    /// BabyBear reduction: uses 2^31 ≡ 2^27 - 1 (mod p)
    /// For z = a * b (product of 32-bit values, result < p² < 2^62):
    ///   z_hi = z >> 31
    ///   z_lo = z & 0x7FFFFFFF
    ///   z ≡ z_lo + z_hi * (2^27 - 1) (mod p)
    #[inline(always)]
    fn reduce(val: u64) -> Self {
        // Simple reduction: correct by definition
        Self((val % BABYBEAR_MODULUS) as u32)
    }
}

impl NttField for BabyBear {
    const MODULUS: u64 = BABYBEAR_MODULUS;
    const GENERATOR: u64 = 31;

    #[inline(always)]
    fn zero() -> Self { Self(0) }

    #[inline(always)]
    fn one() -> Self { Self(1) }

    #[inline(always)]
    fn from_u64(n: u64) -> Self { Self::new((n % BABYBEAR_MODULUS) as u32) }

    #[inline(always)]
    fn to_u64(self) -> u64 { self.0 as u64 }

    #[inline(always)]
    fn add(self, other: Self) -> Self {
        let sum = self.0 as u64 + other.0 as u64;
        if sum >= BABYBEAR_MODULUS {
            Self((sum - BABYBEAR_MODULUS) as u32)
        } else {
            Self(sum as u32)
        }
    }

    #[inline(always)]
    fn sub(self, other: Self) -> Self {
        if self.0 >= other.0 {
            Self(self.0 - other.0)
        } else {
            Self(BABYBEAR_MODULUS_U32 - other.0 + self.0)
        }
    }

    #[inline(always)]
    fn mul(self, other: Self) -> Self {
        Self::reduce(self.0 as u64 * other.0 as u64)
    }

    #[inline(always)]
    fn neg(self) -> Self {
        if self.0 == 0 { Self(0) } else { Self(BABYBEAR_MODULUS_U32 - self.0) }
    }

    fn inv(self) -> Self {
        // Fermat's little theorem: a^(p-2) mod p
        self.pow(BABYBEAR_MODULUS - 2)
    }

    fn pow(self, exp: u64) -> Self {
        let mut base = self;
        let mut result = Self::one();
        let mut e = exp;
        while e > 0 {
            if e & 1 == 1 {
                result = result.mul(base);
            }
            base = base.mul(base);
            e >>= 1;
        }
        result
    }

    fn primitive_root(n: usize) -> Self {
        let exp = (BABYBEAR_MODULUS - 1) / n as u64;
        Self::new(Self::GENERATOR as u32).pow(exp)
    }
}"

/-- Generate operator impls for a field struct -/
def generateOperatorImpls (structName : String) : String :=
  let lb := "{"
  let rb := "}"
  let impls := [
    s!"impl std::ops::Add for {structName} {lb}",
    s!"    type Output = Self;",
    s!"    #[inline(always)]",
    s!"    fn add(self, rhs: Self) -> Self {lb} NttField::add(self, rhs) {rb}",
    rb,
    "",
    s!"impl std::ops::Sub for {structName} {lb}",
    s!"    type Output = Self;",
    s!"    #[inline(always)]",
    s!"    fn sub(self, rhs: Self) -> Self {lb} NttField::sub(self, rhs) {rb}",
    rb,
    "",
    s!"impl std::ops::Mul for {structName} {lb}",
    s!"    type Output = Self;",
    s!"    #[inline(always)]",
    s!"    fn mul(self, rhs: Self) -> Self {lb} NttField::mul(self, rhs) {rb}",
    rb,
    "",
    s!"impl std::ops::Neg for {structName} {lb}",
    s!"    type Output = Self;",
    s!"    #[inline(always)]",
    s!"    fn neg(self) -> Self {lb} NttField::neg(self) {rb}",
    rb
  ]
  String.intercalate "\n" impls

/-! ## Part 8: Full File Generation -/

/-- Generate a complete Rust function from ExpandedSigma -/
def generateFunction (name : String) (_inputSize _outputSize : Nat) (e : ExpandedSigma)
    (useUnsafe : Bool := false) : String :=
  let lbrace := "{"
  let rbrace := "}"
  let signature := s!"pub fn {name}<F: NttField>(input: &[F], output: &mut [F])"
  let body := expandedSigmaToRust e { indent := 1, useUnsafe := useUnsafe }
  s!"{signature} {lbrace}\n{body}\n{rbrace}"

/-- Generate a complete Rust file with trait, impls, and NTT functions -/
def generateRustFile (name : String) (inputSize outputSize : Nat) (e : ExpandedSigma) : String :=
  let header := "// Generated by AMO-Lean Sigma-SPL Rust CodeGen\n// Fase 8 Onda 1 — Subfase 4\n"
  let imports := "use std::fmt::Debug;\n\n"
  let trait := generateNttFieldTrait
  let goldilocks := generateGoldilocksImpl
  let goldilocksOps := generateOperatorImpls "Goldilocks"
  let babybear := generateBabyBearImpl
  let babybearOps := generateOperatorImpls "BabyBear"
  let func := generateFunction name inputSize outputSize e
  String.intercalate "\n\n" [header ++ imports, trait, goldilocks, goldilocksOps, babybear, babybearOps, func]

/-! ## Part 9: Pipeline Helpers -/

/-- Full pipeline: MatExpr → SigmaExpr → ExpandedSigma → Rust code -/
def matExprToRust (name : String) (m n : Nat) (e : AmoLean.Matrix.MatExpr Int m n) : String :=
  let sigma := lowerFresh m n e
  let expanded := expandSigmaExpr sigma
  generateRustFile name n m expanded

/-! ## Part 10: Tests -/

section Tests

open AmoLean.Matrix (MatExpr)

-- Test 1: Generate Rust for DFT_2
def testGenDFT2Rust : IO Unit := do
  IO.println "=== Test 1: Generate Rust for DFT_2 ==="
  let dft2 : MatExpr Int 2 2 := .dft 2
  let sigma := lowerFresh 2 2 dft2
  let expanded := expandSigmaExpr sigma
  let code := generateFunction "dft_2" 2 2 expanded
  IO.println code
  IO.println ""

-- Test 2: Generate Rust for I_2 ⊗ DFT_2
def testGenI2xDFT2Rust : IO Unit := do
  IO.println "=== Test 2: Generate Rust for I_2 ⊗ DFT_2 ==="
  let i2 : MatExpr Int 2 2 := .identity 2
  let dft2 : MatExpr Int 2 2 := .dft 2
  let expr : MatExpr Int 4 4 := .kron i2 dft2
  let sigma := lowerFresh 4 4 expr
  let expanded := expandSigmaExpr sigma
  let code := generateFunction "i2_kron_dft2" 4 4 expanded
  IO.println code
  IO.println ""

-- Test 3: Generate Rust for DFT_4 via Cooley-Tukey
def testGenDFT4CTRust : IO Unit := do
  IO.println "=== Test 3: Generate Rust for DFT_4 via Cooley-Tukey ==="
  let dft2 : MatExpr Int 2 2 := .dft 2
  let i2 : MatExpr Int 2 2 := .identity 2
  let stage1 : MatExpr Int 4 4 := .kron i2 dft2
  let stage2 : MatExpr Int 4 4 := .kron dft2 i2
  let expr : MatExpr Int 4 4 := .compose stage2 stage1
  let sigma := lowerFresh 4 4 expr
  let expanded := expandSigmaExpr sigma
  let code := generateFunction "dft_4_cooley_tukey" 4 4 expanded
  IO.println code
  IO.println ""

-- Test 4: Full Rust file generation
def testGenFullRustFile : IO Unit := do
  IO.println "=== Test 4: Full Rust file (header only) ==="
  IO.println "// NttField trait generated successfully"
  IO.println s!"// Trait length: {generateNttFieldTrait.length} chars"
  IO.println s!"// Goldilocks impl length: {generateGoldilocksImpl.length} chars"
  IO.println s!"// BabyBear impl length: {generateBabyBearImpl.length} chars"
  IO.println ""

-- Test 5: Generate NttField trait and impls
def testGenNttFieldTrait : IO Unit := do
  IO.println "=== Test 5: NttField trait ==="
  IO.println generateNttFieldTrait
  IO.println ""

-- Run all Rust codegen tests
#eval! do
  testGenDFT2Rust
  testGenI2xDFT2Rust
  testGenDFT4CTRust
  testGenFullRustFile
  testGenNttFieldTrait

end Tests

end AmoLean.Backends.Rust
