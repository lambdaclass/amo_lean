/-
  Emit profiled NTT C code with CNTVCT per-stage timing (N36.5a).
  Usage: lake env lean --run Tests/benchmark/emit_profiled.lean babybear 16
-/
import AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline

open AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline
open AmoLean.EGraph.Verified.Bitwise (arm_neon_simd HardwareCost)
open AmoLean.EGraph.Verified.Bitwise.UltraPipeline (UltraConfig)

def getField (name : String) : Option FieldConfig :=
  match name with
  | "babybear" => some babybearConfig
  | "koalabear" => some koalabearConfig
  | "mersenne31" => some mersenne31Config
  | _ => none

/-- Build UltraConfig with profiled=true. -/
private def fieldConfigToProfiledConfig (fc : FieldConfig) (hw : HardwareCost) : UltraConfig :=
  { hw := hw
    k := fc.k
    c := fc.cNat
    mu := fc.muNat
    targetColor := if hw.isSimd then 2 else 1
    useSqdmulh := hw.isSimd
    profiled := true }

def main (args : List String) : IO Unit := do
  let field := args.getD 0 "babybear"
  let logNStr := args.getD 1 "16"
  let some fc := getField field
    | IO.eprintln s!"Unknown field: {field}"; return
  let some logN := logNStr.toNat?
    | IO.eprintln s!"Invalid logN: {logNStr}"; return
  let hw := arm_neon_simd
  let n := 2^logN
  let ucfg := fieldConfigToProfiledConfig fc hw
  let (seedGraph, stageIds) :=
    AmoLean.EGraph.Verified.Bitwise.BoundIntegration.mkFullNTTSeedGraph fc.pNat logN
  let seedRules :=
    AmoLean.EGraph.Verified.Bitwise.ReductionAlternativeRules.reductionAlternativeRules fc.pNat
  let (nttBody, _, _) :=
    AmoLean.EGraph.Verified.Bitwise.UltraPipeline.ultraPipeline seedGraph seedRules fc.pNat n ucfg
      s!"{fc.name.toLower}_ntt_ultra" (some stageIds)
  -- Emit standalone profiled program
  let rLit := "4294967296ULL"
  IO.println s!"#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <time.h>

{nttBody}

int main(void) \{
    size_t n = {n}, logn = {logN};
    size_t tw_sz = n * logn;
    int32_t *data = (int32_t*)aligned_alloc(64, n * sizeof(int32_t));
    int32_t *orig = (int32_t*)aligned_alloc(64, n * sizeof(int32_t));
    int32_t *tw = (int32_t*)malloc(tw_sz * sizeof(int32_t));
    int32_t *tw_mont = (int32_t*)malloc(tw_sz * sizeof(int32_t));
    int32_t *mu_tw = (int32_t*)malloc(tw_sz * sizeof(int32_t));
    /* Init */
    for(size_t i=0;i<n;i++) orig[i]=(int32_t)((i*1000000007ULL)%{fc.pNat}U);
    uint64_t omega_n = 1; /* simplified — just needs valid values for profiling */
    for(size_t i=0;i<tw_sz;i++) tw[i]=(int32_t)((i*7+31)%{fc.pNat}U);
    for(size_t i=0;i<tw_sz;i++) tw_mont[i]=(int32_t)(((uint64_t)(uint32_t)tw[i]*{rLit})%{fc.pNat}U);
    for(size_t i=0;i<tw_sz;i++) mu_tw[i]=(int32_t)(((uint64_t)(uint32_t)tw_mont[i]*(uint64_t){fc.muLit})&0xFFFFFFFFULL);
    /* Warmup */
    memcpy(data, orig, n*sizeof(int32_t));
    {fc.name.toLower}_ntt_ultra(data, tw_mont, mu_tw);
    /* Profiled run */
    const int ITERS = 200;
    for(int it=0;it<ITERS;it++) \{
        memcpy(data, orig, n*sizeof(int32_t));
        {fc.name.toLower}_ntt_ultra(data, tw_mont, mu_tw);
    }
    free(data); free(orig); free(tw); free(tw_mont); free(mu_tw);
    return 0;
}"
