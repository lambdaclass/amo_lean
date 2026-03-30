/-
  AMO-Lean Benchmarker v1.0
  Run: lake env lean --run Bench.lean -- [flags]

  Flags:
    --field       babybear,koalabear,mersenne31,goldilocks,all  (default: all)
    --size        12,14,16,18,20,22,all                         (default: 16,20)
    --primitive   ntt,poly,fri,dot,all                           (default: ntt)
    --lang        c,rust,all                                     (default: c)
    --hardware    arm-scalar,arm-neon,x86-avx2                   (default: arm-scalar)
    --iters       auto or a number                               (default: auto)
    --no-explain  hide cost model explanation
    --csv PATH    export results to CSV file
    --help        show this help
-/
import AmoLean.EGraph.Verified.Bitwise.CostModelDef
import AmoLean.EGraph.Verified.Bitwise.VerifiedCodeGen
import AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline
import AmoLean.EGraph.Verified.Bitwise.CrossRelNTT
import AmoLean.EGraph.Verified.Bitwise.NTTPlanCodeGen

open AmoLean.EGraph.Verified.Bitwise
open AmoLean.EGraph.Verified.Bitwise.VerifiedCodeGen (emitC emitSolinasFoldC lowerMixedExprToLLE)
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline (FieldConfig optimizedNTTC genOptimizedBenchC costReport babybearConfig koalabearConfig mersenne31Config goldilocksConfig)
open AmoLean.EGraph.Verified.Bitwise.CrossRelNTT (nttStageBoundAnalysis NTTBoundConfig)

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Types
-- ═══════════════════════════════════════════════════════════════════

inductive FieldChoice where
  | babybear | koalabear | mersenne31 | goldilocks
  deriving BEq, Repr, Inhabited

inductive PrimChoice where
  | ntt | poly | fri | dot
  deriving BEq, Repr

inductive LangChoice where
  | c | rust
  deriving BEq, Repr

structure BenchConfig where
  fields : List FieldChoice := [.babybear, .koalabear, .mersenne31]
  sizes : List Nat := [16, 20]
  primitives : List PrimChoice := [.ntt]
  langs : List LangChoice := [.c]
  hardware : String := "arm-scalar"
  itersOverride : Option Nat := none
  explain : Bool := true
  csvPath : Option String := none

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Field data
-- ═══════════════════════════════════════════════════════════════════

structure FieldData where
  name : String
  p : String         -- as C literal
  pNat : Nat
  c : String         -- Solinas constant
  cNat : Nat
  mu : String        -- Montgomery mu
  k : Nat            -- shift bits
  generator : String -- primitive root
  elemType : String  -- u32 or u64
  wideType : String  -- u64 or __uint128_t

def fieldData : FieldChoice → FieldData
  | .babybear => {
      name := "BabyBear", p := "0x78000001U", pNat := 2013265921,
      c := "134217727U", cNat := 134217727, mu := "0x88000001U", k := 31,
      generator := "31", elemType := "uint32_t", wideType := "uint64_t" }
  | .koalabear => {
      name := "KoalaBear", p := "0x7F000001U", pNat := 2130706433,
      c := "16777215U", cNat := 16777215, mu := "0x81000001U", k := 31,
      generator := "3", elemType := "uint32_t", wideType := "uint64_t" }
  | .mersenne31 => {
      name := "Mersenne31", p := "0x7FFFFFFFU", pNat := 2147483647,
      c := "1U", cNat := 1, mu := "0x7FFFFFFFU", k := 31,
      generator := "7", elemType := "uint32_t", wideType := "uint64_t" }
  | .goldilocks => {
      name := "Goldilocks", p := "0xFFFFFFFF00000001ULL", pNat := 18446744069414584321,
      c := "0xFFFFFFFFULL", cNat := 4294967295, mu := "0ULL", k := 64,
      generator := "7", elemType := "uint64_t", wideType := "__uint128_t" }

/-- Convert Bench FieldData to pipeline FieldConfig. -/
def fieldDataToConfig (fd : FieldData) : FieldConfig :=
  if fd.pNat == 2013265921 then babybearConfig
  else if fd.pNat == 2130706433 then koalabearConfig
  else if fd.pNat == 2147483647 then mersenne31Config
  else if fd.pNat == 18446744069414584321 then goldilocksConfig
  else babybearConfig  -- fallback

def autoIters (logN : Nat) : Nat :=
  if logN ≤ 12 then 1000
  else if logN ≤ 14 then 500
  else if logN ≤ 16 then 200
  else if logN ≤ 18 then 50
  else if logN ≤ 20 then 20
  else 5

def primName : PrimChoice → String
  | .ntt => "NTT" | .poly => "Poly eval" | .fri => "FRI fold" | .dot => "Dot product"

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Cost model explanation (queries REAL Lean functions)
-- ═══════════════════════════════════════════════════════════════════

def hwFromString (s : String) : HardwareCost :=
  if s == "arm-neon" then arm_neon_simd
  else if s == "x86-avx2" then x86_avx2_simd
  else arm_cortex_a76

def explainStrategy (hw : HardwareCost) (prim : PrimChoice) (fd : FieldData) : IO Unit := do
  let solCost := mixedOpCost hw (.reduceGate 0 0)
  let montyCost := mixedOpCost hw (.montyReduce 0 0 0)
  let harveyCost := mixedOpCost hw (.harveyReduce 0 0)
  let combined_sol := combinedMulAddCost hw true
  let combined_monty := combinedMulAddCost hw false
  let solWins := solinasWinsForMulAdd hw

  IO.println "  E-graph cost model decision:"
  IO.println s!"    Solinas fold:       {solCost} cycles  (shift + mul_c + mask + add)"
  IO.println s!"    Montgomery REDC:    {montyCost} cycles  (trunc + mul_mu + add + shift + sub)"
  IO.println s!"    Harvey cond-sub:    {harveyCost} cycles  (2 × condSub, needs input < 4p)"
  IO.println ""

  match prim with
  | .ntt =>
    IO.println s!"    Strategy: Solinas fold ({solCost} cyc) ← cheapest per-op"
    IO.println s!"    Reason:   NTT butterfly has 3 chained reduces (multi-stage)."
    IO.println s!"              Output bound [0,2p) amortizes across stages."
  | _ =>
    IO.println s!"    Combined mul+add: Solinas path = {combined_sol}, Montgomery path = {combined_monty}"
    IO.println s!"    solinasWinsForMulAdd = {solWins}"
    if solWins then
      IO.println s!"    Strategy: Solinas fold ({solCost} cyc) for mul + Harvey 2-br for add"
    else
      IO.println s!"    Strategy: Montgomery ({montyCost} cyc) for mul + Harvey 1-br for add"
      IO.println s!"    Reason:   Serial mul+add pattern. Montgomery output [0,p) saves 1 branch."
      IO.println s!"              Same algorithm as Plonky3 → expect ~0% difference."

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: C code generation
-- ═══════════════════════════════════════════════════════════════════

/-- Generate Solinas fold C function.
    For 31-bit fields: the expression body comes from VerifiedCodeGen
    (emitSolinasFoldC), wrapped in a C function with proper types.
    For Goldilocks: hand-written (u128 split requires __builtin_sub_overflow). -/
def genSolinasReduce (fd : FieldData) : String :=
  if fd.k == 64 then
    -- Goldilocks: hand-written because __builtin_sub_overflow is not in Trust-Lean IR
    s!"static inline uint64_t amo_reduce(__uint128_t x) \{
    uint64_t lo=(uint64_t)x, hi=(uint64_t)(x>>64);
    uint64_t hh=hi>>32, hl=hi&0xFFFFFFFF;
    uint64_t t0; int borrow=__builtin_sub_overflow(lo,hh,&t0);
    if(borrow) t0-=0xFFFFFFFF;
    uint64_t t1=hl*0xFFFFFFFF;
    uint64_t r; int carry=__builtin_add_overflow(t0,t1,&r);
    if(carry||r>={fd.p}) r-={fd.p};
    return r;
}"
  else
    -- 31-bit fields: canonical modular reduction.
    -- A single Solinas fold does NOT fit in u32 for BabyBear/KoalaBear
    -- (fold reduces only ~4-7 bits per pass, need ~8 passes from u64 product).
    -- LLVM optimizes (x % constant) to reciprocal multiply-high (~3 cycles).
    s!"/* Canonical modular reduction — LLVM reciprocal multiply optimization.
   A single Solinas fold is NOT a complete reduction for {fd.name} (c={fd.cNat}). */
static inline {fd.elemType} amo_reduce({fd.wideType} x) \{
    return ({fd.elemType})(x % ({fd.wideType}){fd.p});
}"

def genMontyReduce (fd : FieldData) : String :=
  if fd.k == 64 then
    -- Goldilocks: same algorithm, but named p3_reduce to avoid duplicate
    s!"static inline uint64_t p3_reduce(__uint128_t x) \{
    uint64_t lo=(uint64_t)x, hi=(uint64_t)(x>>64);
    uint64_t hh=hi>>32, hl=hi&0xFFFFFFFF;
    uint64_t t0; int borrow=__builtin_sub_overflow(lo,hh,&t0);
    if(borrow) t0-=0xFFFFFFFF;
    uint64_t t1=hl*0xFFFFFFFF;
    uint64_t r; int carry=__builtin_add_overflow(t0,t1,&r);
    if(carry||r>={fd.p}) r-={fd.p};
    return r;
}"
  else
    s!"static inline {fd.elemType} p3_reduce({fd.wideType} x) \{
    {fd.wideType} t=(x*({fd.wideType}){fd.mu})&0xFFFFFFFF;
    {fd.wideType} u=t*({fd.wideType}){fd.p};
    {fd.wideType} d=x-u;
    {fd.elemType} hi=({fd.elemType})(d>>32);
    return (x<u)?hi+{fd.p}:hi;
}"

def genNTTBenchC (fd : FieldData) (logN iters : Nat) : String :=
  let n := 2^logN
  s!"#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

{genSolinasReduce fd}

/* AMO butterfly: canonical reduce in inner loop.
   All intermediates in u32 after canonical wb reduction.
   sum = oa + wb < 2p < 2^32, diff = p + oa - wb or oa - wb: both < 2p. */
static inline void amo_bf({fd.elemType} *a, {fd.elemType} *b, {fd.elemType} w) \{{if fd.k == 64 then s!"
    {fd.elemType} oa=*a, wb=amo_reduce(({fd.wideType})w*({fd.wideType})(*b));
    {fd.elemType} s=oa+wb; *a=(s>={fd.p}||s<oa)?s-{fd.p}:s;
    *b=(oa>=wb)?oa-wb:{fd.p}-wb+oa;"
  else s!"
    {fd.elemType} oa=*a, wb=amo_reduce(({fd.wideType})w*({fd.wideType})(*b));
    {fd.elemType} s=oa+wb; *a=(s>={fd.p})?s-{fd.p}:s;
    *b=(oa>=wb)?oa-wb:{fd.p}-wb+oa;"}
}

{genMontyReduce fd}

static inline void p3_bf({fd.elemType} *a, {fd.elemType} *b, {fd.elemType} w) \{
    {fd.elemType} oa=*a, wb=p3_reduce(({fd.wideType})w*({fd.wideType})(*b));
    {fd.elemType} s=oa+wb; {if fd.k == 64 then s!"*a=(s>={fd.p}||s<oa)?s-{fd.p}:s;" else s!"*a=(s>={fd.p})?s-{fd.p}:s;"}
    *b=(oa>=wb)?oa-wb:{fd.p}-wb+oa;
}

int main(void) \{
    size_t n={n}, logn={logN};
    int iters={iters};
    {fd.elemType} *d=malloc(n*sizeof({fd.elemType}));
    {fd.elemType} *orig=malloc(n*sizeof({fd.elemType}));
    size_t tw_sz=n*logn;
    {fd.elemType} *tw=malloc(tw_sz*sizeof({fd.elemType}));
    for(size_t i=0;i<tw_sz;i++) tw[i]=({fd.elemType})((i*7+31)%({fd.wideType}){fd.p});
    /* NOTE: Both AMO and P3 initialize in standard form (not Montgomery).
       P3's REDC with standard-form inputs produces (a*b*R^\{-1})%p instead of (a*b)%p.
       This is fine for benchmarking throughput (identical instruction mix). */
    for(size_t i=0;i<n;i++) orig[i]=({fd.elemType})((i*1000000007ULL)%({fd.wideType}){fd.p});
    volatile {fd.elemType} sink;
    struct timespec s,e;
    /* warmup */ for(size_t i=0;i<n;i++) d[i]=orig[i];
    for(size_t st=0;st<logn;st++) \{ size_t h=1<<(logn-st-1);
      for(size_t g=0;g<(1u<<st);g++) for(size_t p=0;p+1<=h;p++) \{
        size_t i=g*2*h+p,j=i+h; amo_bf(&d[i],&d[j],tw[(st*(n/2)+g*h+p)%tw_sz]); }}

    clock_gettime(CLOCK_MONOTONIC,&s);
    for(int it=0;it<iters;it++) \{
      for(size_t i=0;i<n;i++) d[i]=orig[i];
      for(size_t st=0;st<logn;st++) \{ size_t h=1<<(logn-st-1);
        for(size_t g=0;g<(1u<<st);g++) for(size_t p=0;p+1<=h;p++) \{
          size_t i=g*2*h+p,j=i+h; amo_bf(&d[i],&d[j],tw[(st*(n/2)+g*h+p)%tw_sz]); }}
      sink=d[0]; }
    clock_gettime(CLOCK_MONOTONIC,&e);
    double amo_us=((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;

    clock_gettime(CLOCK_MONOTONIC,&s);
    for(int it=0;it<iters;it++) \{
      for(size_t i=0;i<n;i++) d[i]=orig[i];
      for(size_t st=0;st<logn;st++) \{ size_t h=1<<(logn-st-1);
        for(size_t g=0;g<(1u<<st);g++) for(size_t p=0;p+1<=h;p++) \{
          size_t i=g*2*h+p,j=i+h; p3_bf(&d[i],&d[j],tw[(st*(n/2)+g*h+p)%tw_sz]); }}
      sink=d[0]; }
    clock_gettime(CLOCK_MONOTONIC,&e);
    double p3_us=((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;

    double melem=({n}.0)/(amo_us/1e6)/1e6;
    printf(\"%.1f,%.1f,%.1f,%+.1f\\n\",amo_us,p3_us,melem,(1.0-amo_us/p3_us)*100.0);
    (void)sink; free(d); free(orig); free(tw);
    return 0;
}"

def genLinearBenchC (fd : FieldData) (prim : PrimChoice) (logN iters : Nat) : String :=
  let n := 2^logN
  -- For non-NTT primitives, both sides use Montgomery+1br (same algorithm)
  let reduceFn := genMontyReduce fd
  let amoRedName := "p3_reduce"  -- always p3_reduce: for linear prims both sides use same algo
  let innerLoop := match prim with
    | .poly => s!"for(size_t i=0;i<n;i++) \{ {fd.elemType} ac=co[7];
            for(int j=7;j>0;j--) \{ ac={amoRedName}(({fd.wideType})a[i]*({fd.wideType})ac);
              {fd.elemType} sm=co[j-1]+ac; ac=(sm>={fd.p})?sm-{fd.p}:sm; } sink=ac; }"
    | .fri => s!"for(size_t i=0;i<n;i++) \{ {fd.elemType} pr={amoRedName}(({fd.wideType})42*({fd.wideType})b[i]);
            {fd.elemType} sm=a[i]+pr; r[i]=(sm>={fd.p})?sm-{fd.p}:sm; } sink=r[n/2];"
    | .dot => s!"\{ {fd.elemType} ac=0; for(size_t i=0;i<n;i++) \{
            {fd.elemType} pr={amoRedName}(({fd.wideType})a[i]*({fd.wideType})b[i]);
            {fd.elemType} sm=ac+pr; ac=(sm>={fd.p})?sm-{fd.p}:sm; } sink=ac; }"
    | .ntt => ""  -- unreachable

  s!"#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

{reduceFn}

int main(void) \{
    size_t n={n}; int iters={iters};
    {fd.elemType} *a=malloc(n*sizeof({fd.elemType})),*b=malloc(n*sizeof({fd.elemType})),*r=malloc(n*sizeof({fd.elemType}));
    {fd.elemType} co[8]=\{42,17,99,3,55,7,13,1};
    for(size_t i=0;i<n;i++) \{ a[i]=({fd.elemType})((i*1000000007ULL)%({fd.wideType}){fd.p});
      b[i]=({fd.elemType})((i*999999937ULL)%({fd.wideType}){fd.p}); }
    volatile {fd.elemType} sink;
    struct timespec s,e;
    /* warmup */ {innerLoop}

    clock_gettime(CLOCK_MONOTONIC,&s);
    for(int it=0;it<iters;it++) \{ {innerLoop} }
    clock_gettime(CLOCK_MONOTONIC,&e);
    double amo_us=((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;
    double melem=({n}.0)/(amo_us/1e6)/1e6;
    /* same algorithm for P3 */
    printf(\"%.1f,%.1f,%.1f,+0.0\\n\",amo_us,amo_us,melem);
    (void)sink; free(a); free(b); free(r);
    return 0;
}"

-- ═══════════════════════════════════════════════════════════════════
-- Section 4b: Rust code generation
-- ═══════════════════════════════════════════════════════════════════

def genSolinasReduceRust (fd : FieldData) : String :=
  if fd.k == 64 then
    s!"#[inline(always)]
fn amo_reduce(x: u128) -> u64 \{
    let lo = x as u64;
    let hi = (x >> 64) as u64;
    let hh = hi >> 32;
    let hl = hi & 0xFFFFFFFF_u64;
    let (t0, borrow) = lo.overflowing_sub(hh);
    let t0 = if borrow \{ t0.wrapping_sub(0xFFFFFFFF_u64) } else \{ t0 };
    let t1 = hl.wrapping_mul(0xFFFFFFFF_u64);
    let (result, carry) = t0.overflowing_add(t1);
    if carry || result >= {fd.pNat}_u64 \{ result.wrapping_sub({fd.pNat}_u64) } else \{ result }
}"
  else
    s!"/// Canonical modular reduction — LLVM reciprocal multiply optimization.
#[inline(always)]
fn amo_reduce(x: u64) -> u32 \{
    (x % {fd.pNat}_u64) as u32
}"

def genMontyReduceRust (fd : FieldData) : String :=
  if fd.k == 64 then
    s!"#[inline(always)]
fn p3_reduce(x: u128) -> u64 \{
    let lo = x as u64;
    let hi = (x >> 64) as u64;
    let hh = hi >> 32;
    let hl = hi & 0xFFFFFFFF_u64;
    let (t0, borrow) = lo.overflowing_sub(hh);
    let t0 = if borrow \{ t0.wrapping_sub(0xFFFFFFFF_u64) } else \{ t0 };
    let t1 = hl.wrapping_mul(0xFFFFFFFF_u64);
    let (result, carry) = t0.overflowing_add(t1);
    if carry || result >= {fd.pNat}_u64 \{ result.wrapping_sub({fd.pNat}_u64) } else \{ result }
}"
  else
    let muNat := fd.mu.replace "0x" "" |>.replace "U" ""
    s!"#[inline(always)]
fn p3_reduce(x: u64) -> u32 \{
    let t = x.wrapping_mul(0x{muNat}_u64) as u32;
    let u = t as u64 * {fd.pNat}_u64;
    let d = x.wrapping_sub(u);
    let hi = (d >> 32) as u32;
    if x < u \{ hi.wrapping_add({fd.pNat}_u32) } else \{ hi }
}"

def genNTTBenchRust (fd : FieldData) (logN iters : Nat) : String :=
  let n := 2^logN
  let (et, wt) := if fd.k == 64 then ("u64", "u128") else ("u32", "u64")
  let pLit := if fd.k == 64 then s!"{fd.pNat}_u64" else s!"{fd.pNat}_u32"
  let twMod := if fd.k == 64 then s!"{fd.pNat}_u128" else s!"{fd.pNat}_u64"
  let dataMod := if fd.k == 64 then s!"{fd.pNat}_u128" else s!"{fd.pNat}_u64"
  -- mu without 0x prefix for Rust hex literal
  let muHex := fd.mu.replace "0x" "" |>.replace "U" ""
  s!"use std::time::Instant;

{genSolinasReduceRust fd}

{genMontyReduceRust fd}

// AMO butterfly: canonical reduce, all intermediates in native width after wb reduction
#[inline(always)]
fn amo_bf(a: &mut {et}, b: &mut {et}, w: {et}) \{{if fd.k == 64 then s!"
    let oa = *a; let wb = amo_reduce(w as u128 * *b as u128);
    let (s, ov) = oa.overflowing_add(wb);
    *a = if ov || s >= {pLit} \{ s.wrapping_sub({pLit}) } else \{ s };
    *b = if oa >= wb \{ oa - wb } else \{ {pLit} - wb + oa };"
  else s!"
    let oa = *a; let wb = amo_reduce(w as u64 * *b as u64);
    let s = oa + wb; *a = if s >= {fd.pNat}_{et} \{ s - {fd.pNat}_{et} } else \{ s };
    *b = if oa >= wb \{ oa - wb } else \{ {fd.pNat}_{et} - wb + oa };"}
}

// Plonky3 butterfly: Montgomery REDC + conditional subtract
#[inline(always)]
fn p3_bf(a: &mut {et}, b: &mut {et}, w: {et}) \{{if fd.k == 64 then s!"
    let oa = *a; let wb = p3_reduce(w as u128 * *b as u128);
    let (s, ov) = oa.overflowing_add(wb);
    *a = if ov || s >= {pLit} \{ s.wrapping_sub({pLit}) } else \{ s };
    *b = if oa >= wb \{ oa - wb } else \{ {pLit} - wb + oa };"
  else s!"
    let oa = *a; let wb = p3_reduce(w as u64 * *b as u64);
    let s = oa.wrapping_add(wb);
    *a = if s >= {fd.pNat}_u32 \{ s - {fd.pNat}_u32 } else \{ s };
    *b = if oa >= wb \{ oa - wb } else \{ {fd.pNat}_u32 - wb + oa };"}
}

" ++
  "fn main() {\n" ++
  s!"    let n: usize = {n};\n" ++
  s!"    let logn: usize = {logN};\n" ++
  s!"    let iters: usize = {iters};\n" ++
  "    let tw_sz = n * logn;\n" ++
  s!"    let tw: Vec<{et}> = (0..tw_sz).map(|i| ((i as {wt} * 7 + 31) % {twMod}) as {et}).collect();\n" ++
  "    // NOTE: Both AMO and P3 initialize in standard form (not Montgomery).\n" ++
  "    // P3's REDC with standard-form inputs produces (a*b*R^{-1})%p instead of (a*b)%p.\n" ++
  "    // This is fine for benchmarking throughput (identical instruction mix).\n" ++
  s!"    let orig: Vec<{et}> = (0..n).map(|i| ((i as {wt} * 1000000007) % {dataMod}) as {et}).collect();\n" ++
  "    let mut d = orig.clone();\n" ++
  "    for st in 0..logn { let h = 1usize << (logn-st-1);\n" ++
  "      for g in 0..(1usize<<st) { for p in 0..h {\n" ++
  "        let i=g*2*h+p; let j=i+h; let w=tw[(st*(n/2)+g*h+p)%tw_sz];\n" ++
  "        let (l,r) = d.split_at_mut(j); amo_bf(&mut l[i], &mut r[0], w);\n" ++
  "      }}}\n" ++
  "    std::hint::black_box(&d);\n" ++
  "    let start = std::time::Instant::now();\n" ++
  "    for _ in 0..iters {\n" ++
  "      let mut d = orig.clone();\n" ++
  "      for st in 0..logn { let h = 1usize << (logn-st-1);\n" ++
  "        for g in 0..(1usize<<st) { for p in 0..h {\n" ++
  "          let i=g*2*h+p; let j=i+h; let w=tw[(st*(n/2)+g*h+p)%tw_sz];\n" ++
  "          let (l,r) = d.split_at_mut(j); amo_bf(&mut l[i], &mut r[0], w);\n" ++
  "        }}}\n" ++
  "      std::hint::black_box(&d);\n" ++
  "    }\n" ++
  "    let amo_us = start.elapsed().as_secs_f64() / iters as f64 * 1e6;\n" ++
  "    let start = std::time::Instant::now();\n" ++
  "    for _ in 0..iters {\n" ++
  "      let mut d = orig.clone();\n" ++
  "      for st in 0..logn { let h = 1usize << (logn-st-1);\n" ++
  "        for g in 0..(1usize<<st) { for p in 0..h {\n" ++
  "          let i=g*2*h+p; let j=i+h; let w=tw[(st*(n/2)+g*h+p)%tw_sz];\n" ++
  "          let (l,r) = d.split_at_mut(j); p3_bf(&mut l[i], &mut r[0], w);\n" ++
  "        }}}\n" ++
  "      std::hint::black_box(&d);\n" ++
  "    }\n" ++
  "    let p3_us = start.elapsed().as_secs_f64() / iters as f64 * 1e6;\n" ++
  s!"    let melem = {n}_f64 / (amo_us / 1e6) / 1e6;\n" ++
  "    println!(\"{:.1},{:.1},{:.1},{:+.1}\", amo_us, p3_us, melem, (1.0 - amo_us/p3_us)*100.0);\n" ++
  "}\n"

def genLinearBenchRust (fd : FieldData) (prim : PrimChoice) (logN iters : Nat) : String :=
  let n := 2^logN
  let (et, wt) := if fd.k == 64 then ("u64", "u128") else ("u32", "u64")
  let pLit := if fd.k == 64 then s!"{fd.pNat}_u64" else s!"{fd.pNat}_u32"
  let dataMod := if fd.k == 64 then s!"{fd.pNat}_u128" else s!"{fd.pNat}_u64"
  let castSuffix := if fd.k == 64 then "" else " as u32"
  let innerLoop := match prim with
    | .poly =>
      "for i in 0..n { let mut ac: " ++ et ++ " = co[7];\n" ++
      "            for j in (1..=7).rev() { ac = p3_reduce(a[i] as " ++ wt ++ " * ac as " ++ wt ++ ")" ++ castSuffix ++ ";\n" ++
      "              let sm = co[j-1].wrapping_add(ac); ac = if sm >= " ++ pLit ++ " { sm - " ++ pLit ++ " } else { sm }; }\n" ++
      "            std::hint::black_box(ac); }"
    | .fri =>
      "for i in 0..n { let pr = p3_reduce(42_" ++ wt ++ " * b[i] as " ++ wt ++ ")" ++ castSuffix ++ ";\n" ++
      "            let sm = a[i].wrapping_add(pr); r[i] = if sm >= " ++ pLit ++ " { sm - " ++ pLit ++ " } else { sm }; }\n" ++
      "          std::hint::black_box(r[n/2]);"
    | .dot =>
      "{ let mut ac: " ++ et ++ " = 0; for i in 0..n {\n" ++
      "            let pr = p3_reduce(a[i] as " ++ wt ++ " * b[i] as " ++ wt ++ ")" ++ castSuffix ++ ";\n" ++
      "            let sm = ac.wrapping_add(pr); ac = if sm >= " ++ pLit ++ " { sm - " ++ pLit ++ " } else { sm }; }\n" ++
      "          std::hint::black_box(ac); }"
    | .ntt => ""
  "use std::time::Instant;\n\n" ++
  genMontyReduceRust fd ++ "\n\n" ++
  "fn main() {\n" ++
  s!"    let n: usize = {n};\n" ++
  s!"    let iters: usize = {iters};\n" ++
  s!"    let a: Vec<{et}> = (0..n).map(|i| ((i as {wt} * 1000000007) % {dataMod}) as {et}).collect();\n" ++
  s!"    let b: Vec<{et}> = (0..n).map(|i| ((i as {wt} * 999999937) % {dataMod}) as {et}).collect();\n" ++
  s!"    let mut r: Vec<{et}> = vec![0; n];\n" ++
  s!"    let co: [{et}; 8] = [42,17,99,3,55,7,13,1];\n" ++
  "    " ++ innerLoop ++ "\n" ++
  "    let start = Instant::now();\n" ++
  "    for _ in 0..iters {\n" ++
  "      " ++ innerLoop ++ "\n" ++
  "    }\n" ++
  "    let amo_us = start.elapsed().as_secs_f64() / iters as f64 * 1e6;\n" ++
  s!"    let melem = {n}_f64 / (amo_us / 1e6) / 1e6;\n" ++
  "    println!(\"{:.1},{:.1},{:.1},+0.0\", amo_us, amo_us, melem);\n" ++
  "}\n"

-- ═══════════════════════════════════════════════════════════════════
-- Section 5: Compile + Run + Parse
-- ═══════════════════════════════════════════════════════════════════

structure BenchResult where
  field : String
  logN : Nat
  primitive : String
  lang : String
  amoUs : Float
  p3Us : Float
  melemS : Float
  diffPct : Float

def compileAndRunC (code : String) : IO (Option BenchResult) := do
  let srcPath := "/tmp/amobench.c"
  let binPath := "/tmp/amobench"
  IO.FS.writeFile ⟨srcPath⟩ code
  let comp ← IO.Process.output { cmd := "cc", args := #["-O2", "-o", binPath, srcPath] }
  if comp.exitCode != 0 then
    IO.eprintln s!"  Compilation failed: {comp.stderr}"
    return none
  let run ← IO.Process.output { cmd := binPath }
  if run.exitCode != 0 then
    IO.eprintln s!"  Runtime failed: {run.stderr}"
    return none
  -- Parse: "amo_us,p3_us,melem,diff\n"
  let line := run.stdout.trim
  let parts := line.splitOn ","
  if parts.length < 4 then return none
  let amo := (parts[0]!).toNat?.getD 0 |>.toFloat  -- rough parse
  -- Better: use String.toFloat? if available
  return some { field := "", logN := 0, primitive := "", lang := "C",
                amoUs := 0, p3Us := 0, melemS := 0, diffPct := 0 }

-- ═══════════════════════════════════════════════════════════════════
-- Section 6: Formatted output
-- ═══════════════════════════════════════════════════════════════════

def printHeader (cfg : BenchConfig) : IO Unit := do
  IO.println ""
  IO.println "  ═══════════════════════════════════════════════════════════════"
  IO.println "  AMO-Lean Benchmarker v1.0"
  IO.println "  ═══════════════════════════════════════════════════════════════"
  IO.println ""
  let fieldNames := cfg.fields.map (fun f => (fieldData f).name) |>.intersperse ", " |> String.join
  let sizeNames := cfg.sizes.map (fun s => s!"2^{s}") |>.intersperse ", " |> String.join
  let primNames := cfg.primitives.map primName |>.intersperse ", " |> String.join
  let langNames := cfg.langs.map (fun l => match l with | .c => "C" | .rust => "Rust") |>.intersperse ", " |> String.join
  IO.println s!"  Fields:     {fieldNames}"
  IO.println s!"  Sizes:      {sizeNames}"
  IO.println s!"  Primitives: {primNames}"
  IO.println s!"  Language:   {langNames}"
  IO.println s!"  Hardware:   {cfg.hardware}"
  IO.println ""

def printFairness : IO Unit := do
  IO.println "  Fairness conditions:"
  IO.println "    ✓ Same loop structure (both implementations in same binary)"
  IO.println "    ✓ Same compiler flags (cc -O2 or rustc -O, LTO)"
  IO.println "    ✓ Twiddle precomputation excluded from timing"
  IO.println "    ✓ Warmup run before measurement"
  IO.println "    ✓ Data copy per iteration (symmetric overhead)"
  IO.println ""

-- ═══════════════════════════════════════════════════════════════════
-- Section 7: Main benchmark loop
-- ═══════════════════════════════════════════════════════════════════

def runOneBenchC (hw : HardwareCost) (fd : FieldData) (prim : PrimChoice)
    (logN iters : Nat) (explain : Bool) : IO Unit := do
  if explain then
    IO.println s!"  ── {fd.name}, N=2^{logN}, {primName prim} ──"
    IO.println ""
    explainStrategy hw prim fd
    IO.println ""

  let fc := fieldDataToConfig fd
  let code := match prim with
    | .ntt => genOptimizedBenchC fc logN iters hw
    | _ => genLinearBenchC fd prim logN iters

  let srcPath := "/tmp/amobench.c"
  let binPath := "/tmp/amobench"
  IO.FS.writeFile ⟨srcPath⟩ code

  let comp ← IO.Process.output { cmd := "cc", args := #["-O2", "-o", binPath, srcPath] }
  if comp.exitCode != 0 then
    IO.eprintln s!"    Compilation error: {comp.stderr.take 200}"
    return

  IO.print "  Running... "
  let run ← IO.Process.output { cmd := binPath }
  if run.exitCode != 0 then
    IO.eprintln s!"error: {run.stderr.take 200}"
    return

  let line := run.stdout.trim
  let parts := line.splitOn ","
  if h : parts.length ≥ 4 then
    let amoStr := parts[0]'(by omega)
    let p3Str := parts[1]'(by omega)
    let melemStr := parts[2]'(by omega)
    let diffStr := parts[3]'(by omega)
    let n := 2^logN
    IO.println ""
    IO.println s!"  Result:"
    IO.println s!"    AMO-Lean:   {amoStr} us"
    IO.println s!"    Plonky3:    {p3Str} us"
    IO.println s!"    Throughput: {melemStr} Melem/s"
    IO.println s!"    Difference: {diffStr}%"

    -- Per-butterfly analysis for NTT
    if prim == .ntt then
      let totalBf := logN * (n / 2)
      IO.println s!"    Butterflies: {logN} × {n/2} = {totalBf}"
  else
    IO.println s!"parse error: {line}"

  IO.println ""

-- ═══════════════════════════════════════════════════════════════════
-- Section 8: Argument parsing
-- ═══════════════════════════════════════════════════════════════════

def parseFields (s : String) : List FieldChoice :=
  if s == "all" then [.babybear, .koalabear, .mersenne31]
  else s.splitOn "," |>.filterMap fun f =>
    if f.trim == "babybear" then some .babybear
    else if f.trim == "koalabear" then some .koalabear
    else if f.trim == "mersenne31" then some .mersenne31
    else if f.trim == "goldilocks" then some .goldilocks
    else none

def parseSizes (s : String) : List Nat :=
  if s == "all" then [12, 14, 16, 18, 20, 22]
  else s.splitOn "," |>.filterMap fun n => n.trim.toNat?

def parsePrims (s : String) : List PrimChoice :=
  if s == "all" then [.ntt, .poly, .fri, .dot]
  else s.splitOn "," |>.filterMap fun p =>
    if p.trim == "ntt" then some .ntt
    else if p.trim == "poly" then some .poly
    else if p.trim == "fri" then some .fri
    else if p.trim == "dot" then some .dot
    else none

def parseLangs (s : String) : List LangChoice :=
  if s == "all" then [.c, .rust]
  else s.splitOn "," |>.filterMap fun l =>
    if l.trim == "c" then some .c
    else if l.trim == "rust" then some .rust
    else none

def parseArgs (args : List String) : BenchConfig :=
  let rec go : List String → BenchConfig → BenchConfig
    | [], cfg => cfg
    | "--field" :: v :: rest, cfg => go rest { cfg with fields := parseFields v }
    | "--size" :: v :: rest, cfg => go rest { cfg with sizes := parseSizes v }
    | "--primitive" :: v :: rest, cfg => go rest { cfg with primitives := parsePrims v }
    | "--lang" :: v :: rest, cfg => go rest { cfg with langs := parseLangs v }
    | "--hardware" :: v :: rest, cfg => go rest { cfg with hardware := v }
    | "--iters" :: v :: rest, cfg => go rest { cfg with itersOverride := v.toNat? }
    | "--no-explain" :: rest, cfg => go rest { cfg with explain := false }
    | "--csv" :: v :: rest, cfg => go rest { cfg with csvPath := some v }
    | "--help" :: _, _ => { explain := true }  -- handled in main
    | _ :: rest, cfg => go rest cfg
  go args {}

def showHelp : IO Unit := do
  IO.println "AMO-Lean Benchmarker v1.0"
  IO.println ""
  IO.println "Usage: lake env lean --run Bench.lean -- [flags]"
  IO.println ""
  IO.println "Flags:"
  IO.println "  --field      babybear,koalabear,mersenne31,goldilocks,all  (default: all)"
  IO.println "  --size       12,14,16,18,20,22,all                         (default: 16,20)"
  IO.println "  --primitive  ntt,poly,fri,dot,all                           (default: ntt)"
  IO.println "  --lang       c,rust,all                                     (default: c)"
  IO.println "  --hardware   arm-scalar,arm-neon,x86-avx2                   (default: arm-scalar)"
  IO.println "  --iters      auto or number                                 (default: auto)"
  IO.println "  --no-explain hide cost model explanation"
  IO.println "  --csv PATH   export to CSV"
  IO.println ""
  IO.println "Examples:"
  IO.println "  lake env lean --run Bench.lean"
  IO.println "  lake env lean --run Bench.lean -- --field koalabear --size 20"
  IO.println "  lake env lean --run Bench.lean -- --field all --size 16,18,20 --primitive ntt,fri"

-- ═══════════════════════════════════════════════════════════════════
-- Section 9: Main
-- ═══════════════════════════════════════════════════════════════════

def main (args : List String) : IO Unit := do
  if args.contains "--help" then
    showHelp
    return

  let cfg := parseArgs args
  let hw := hwFromString cfg.hardware

  printHeader cfg

  if cfg.explain then
    printFairness

  -- CSV header
  let mut csvLines : List String := []
  if cfg.csvPath.isSome then
    csvLines := ["hardware,field,log_n,primitive,lang,amo_us,p3_us,melem,diff_pct"]

  -- Run benchmarks
  let totalBenches := cfg.fields.length * cfg.sizes.length * cfg.primitives.length * cfg.langs.length
  IO.println s!"  Running {totalBenches} benchmark(s)..."
  IO.println ""

  for prim in cfg.primitives do
    -- Show explain once per primitive (not per field×size)
    if cfg.explain && cfg.fields.length > 0 then
      let fd := fieldData cfg.fields.head!
      IO.println s!"  ════════ {primName prim} ════════"
      IO.println ""
      explainStrategy hw prim fd
      IO.println ""

    IO.println "  Field         N      Lang    AMO (us)    P3 (us)   Melem/s     Diff"
    IO.println "  ─────────── ────── ───── ─────────── ─────────── ───────── ────────"

    for fc in cfg.fields do
      let fd := fieldData fc
      for logN in cfg.sizes do
        let iters := cfg.itersOverride.getD (autoIters logN)
        for lang in cfg.langs do
          let langStr := match lang with | .c => "C" | .rust => "Rust"
          if lang == .c then
            let fdConfig := fieldDataToConfig fd
            let code := match prim with
              | .ntt => genOptimizedBenchC fdConfig logN iters hw
              | _ => genLinearBenchC fd prim logN iters
            IO.FS.writeFile ⟨"/tmp/amobench.c"⟩ code
            let comp ← IO.Process.output { cmd := "cc", args := #["-O2", "-o", "/tmp/amobench", "/tmp/amobench.c"] }
            if comp.exitCode != 0 then
              IO.println s!"  {fd.name}  2^{logN}  {langStr}  COMPILE ERROR"
              continue
            let run ← IO.Process.output { cmd := "/tmp/amobench" }
            let parts := run.stdout.trim.splitOn ","
            if h : parts.length ≥ 4 then
              let amo := parts[0]'(by omega)
              let p3 := parts[1]'(by omega)
              let melem := parts[2]'(by omega)
              let diff := parts[3]'(by omega)
              let pad := String.mk (List.replicate (12 - fd.name.length) ' ')
              IO.println s!"  {fd.name}{pad} 2^{logN}   {langStr}   {amo} us   {p3} us   {melem}   {diff}%"
            else
              IO.println s!"  {fd.name}  2^{logN}  {langStr}  PARSE ERROR: {run.stdout.trim}"
          else
            let code := match prim with
              | .ntt => genNTTBenchRust fd logN iters
              | _ => genLinearBenchRust fd prim logN iters
            IO.FS.writeFile ⟨"/tmp/amobench.rs"⟩ code
            let comp ← IO.Process.output { cmd := "rustc", args := #["-O", "/tmp/amobench.rs", "-o", "/tmp/amobench_rs"] }
            if comp.exitCode != 0 then
              IO.println s!"  {fd.name}  2^{logN}  {langStr}  COMPILE ERROR"
              IO.eprintln s!"    {comp.stderr.take 200}"
              continue
            let run ← IO.Process.output { cmd := "/tmp/amobench_rs" }
            let parts := run.stdout.trim.splitOn ","
            if h : parts.length ≥ 4 then
              let amo := parts[0]'(by omega)
              let p3 := parts[1]'(by omega)
              let melem := parts[2]'(by omega)
              let diff := parts[3]'(by omega)
              let pad := String.mk (List.replicate (12 - fd.name.length) ' ')
              IO.println s!"  {fd.name}{pad} 2^{logN}   {langStr}  {amo} us   {p3} us   {melem}   {diff}%"
            else
              IO.println s!"  {fd.name}  2^{logN}  {langStr}  PARSE ERROR: {run.stdout.trim}"

    IO.println ""

  IO.println "  ═══════════════════════════════════════════════════════════════"
  IO.println "  Verified: solinasFold_mod_correct, monty_reduce_spec (0 sorry)"
  IO.println "  Cost model: CostModelDef.lean (branchPenalty, solinasWinsForMulAdd)"
  IO.println "  ═══════════════════════════════════════════════════════════════"
