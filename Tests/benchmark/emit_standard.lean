/-
  Minimal emitter for v3.15.0 standard DFT validation.
  Generates ONLY the NTT function + validation wrapper.
  Bypasses ultraPipeline (too heavy for interpreter).

  Usage: lake env lean --run Tests/benchmark/emit_standard.lean <field> <logN>
-/
import AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen
import AmoLean.EGraph.Verified.Bitwise.NTTPlanSelection

open AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen (emitCFromPlanStandard)
open AmoLean.EGraph.Verified.Bitwise.NTTPlan (mkUniformPlan mkMixedRadixPlan)

def emitStandardC (p k c mu : Nat) (logN : Nat) (funcName : String)
    (useR4 : Bool := false) : String :=
  let n := 2^logN
  -- v3.15.0 B3.5: support both R2 and R4 plans
  -- mkMixedRadixPlan handles odd logN (R4 early + R2 trailing for leftover level)
  let plan := if useR4 then mkMixedRadixPlan p n
    else mkUniformPlan p n .r2 .harvey
  let plan := if k > 32 then
    { plan with stages := plan.stages.map fun s =>
      if s.radix == .r2 then { s with ilpFactor := 2 } else s }
    else plan
  emitCFromPlanStandard plan k c mu funcName

def emitValidationProgram (field : String) (p k c mu g : Nat) (logN : Nat)
    (elemType wideType : String) (useR4 : Bool := false) : String :=
  let n := 2^logN
  let funcName := s!"{field}_ntt_standard"
  let nttCode := emitStandardC p k c mu logN funcName useR4
  let rLit := if k == 64 then "(__uint128_t)1<<64" else "4294967296ULL"
  let pLit := s!"{p}ULL"
  -- Build the complete C program as a single string
  "#include <stdio.h>\n#include <stdint.h>\n#include <stdlib.h>\n\n" ++
  nttCode ++ "\n\n" ++
  s!"static {wideType} mod_pow({wideType} base, {wideType} exp, {wideType} m) " ++ "{\n" ++
  s!"  {wideType} result = 1; base %= m;\n" ++
  "  while (exp > 0) {\n" ++
  s!"    if (exp & 1) result = ({wideType})(((unsigned __int128)result * base) % m);\n" ++
  s!"    base = ({wideType})(((unsigned __int128)base * base) % m);\n" ++
  "    exp >>= 1; } return result; }\n\n" ++
  "int main(void) {\n" ++
  s!"  size_t n={n}, logn={logN};\n" ++
  s!"  {wideType} p_val = ({wideType}){pLit};\n" ++
  s!"  {wideType} omega_n = mod_pow({g}, (p_val - 1) / n, p_val);\n" ++
  s!"  size_t tw_sz = n * logn;\n" ++
  s!"  {elemType} *tw = malloc(tw_sz * sizeof({elemType}));\n" ++
  "  for(size_t st=0; st<logn; st++) {\n" ++
  "    size_t h = 1u << (logn - 1 - st);\n" ++
  "    for(size_t g=0; g<(1u<<st); g++)\n" ++
  "      for(size_t pp=0; pp<h; pp++)\n" ++
  s!"        tw[st*(n/2)+g*h+pp] = ({elemType})mod_pow(omega_n, pp*(1ULL<<st), p_val);\n" ++
  "  }\n" ++
  -- k ≤ 32 (BabyBear): butterfly uses Montgomery REDC → needs Montgomery twiddles (R cancels)
  -- k > 32 (Goldilocks): butterfly uses goldi_reduce128 (PZT mod p) → needs STANDARD twiddles
  (if k > 32 then
    -- Goldilocks: pass standard twiddles directly (goldi_reduce128 is NOT REDC)
    s!"  {elemType} *d = malloc(n * sizeof({elemType}));\n" ++
    s!"  for(size_t i=0; i<n; i++) d[i] = ({elemType})((i * 1000000007ULL) % ({wideType}){pLit});\n" ++
    s!"  {funcName}(d, tw);\n" ++
    s!"  for(size_t i=0; i<n; i++) printf(\"%llu" ++ "\\n\"" ++ s!", (unsigned long long)(({wideType})d[i] % ({wideType}){pLit}));\n" ++
    "  free(d); free(tw);\n"
  else
    -- BabyBear: pass Montgomery twiddles (REDC cancels R factor)
    s!"  {elemType} *tw_mont = malloc(tw_sz * sizeof({elemType}));\n" ++
    s!"  for(size_t i=0; i<tw_sz; i++) tw_mont[i] = ({elemType})((({wideType})tw[i] * ({wideType}){rLit}) % ({wideType}){pLit});\n" ++
    s!"  {elemType} *d = malloc(n * sizeof({elemType}));\n" ++
    s!"  for(size_t i=0; i<n; i++) d[i] = ({elemType})((i * 1000000007ULL) % ({wideType}){pLit});\n" ++
    s!"  {funcName}(d, tw_mont);\n" ++
    s!"  for(size_t i=0; i<n; i++) printf(\"%llu" ++ "\\n\"" ++ s!", (unsigned long long)(({wideType})d[i] % ({wideType}){pLit}));\n" ++
    "  free(d); free(tw); free(tw_mont);\n") ++
  "  return 0;\n}\n"

def main (args : List String) : IO Unit := do
  let useR4 := args.contains "--r4"
  let args' := args.filter (· != "--r4")
  match args' with
  | [field, logNStr] =>
    let some logN := logNStr.toNat?
      | IO.eprintln s!"Invalid logN: {logNStr}" ; return
    let (p, k, c, mu, g, elemType, wideType) := match field with
      | "babybear"   => (2013265921,   31, 134217727,  0x88000001, 31, "int32_t", "int64_t")
      | "goldilocks" => (18446744069414584321, 64, 4294967295, 0, 7, "uint64_t", "__uint128_t")
      | _ => (0, 0, 0, 0, 0, "", "")
    if p == 0 then
      IO.eprintln s!"Unknown field: {field}"
      return
    IO.print (emitValidationProgram field p k c mu g logN elemType wideType useR4)
  | _ =>
    IO.eprintln "Usage: emit_standard <field> <logN>"
