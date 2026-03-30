# Insights: Pipeline Interaction Bugs — Algorithmic x Bitwise Layer Disconnection

**Fecha**: 2026-03-29
**Severity**: CRITICAL
**Descubierto durante**: auditoría de benchmarks Fase 32

## Hallazgo Detonante

`nttStageBoundAnalysis` para KoalaBear 2^20 produce:
- **18 stages LAZY** (sin reducción — los intermediarios caben en u32)
- **2 stages Solinas** (solo los últimos 2 necesitan reducir)

Pero `Bench.lean` aplica Solinas fold en CADA stage. El bound analysis existe, funciona, y nadie lo usa.

Para Goldilocks: Stage 0 usa Harvey (3 ciclos), stages 1-19 usan Solinas. Harvey debería usarse más agresivamente.

## Los 18 Bugs Encontrados

### CRÍTICOS (bloquean toda optimización)

**Bug 1.1: Bench.lean bypassa completamente el pipeline de optimización**
- `genNTTBenchC` (Bench.lean:186) emite C hardcodeado
- NO importa OptimizedNTTPipeline, NTTPlanSelection, BoundIntegration
- `genOptimizedBenchC` existe como drop-in replacement pero nunca se llama
- **Fix**: import + swap call (~50 LOC)

**Bug 1.2: optimizedNTTC corre el e-graph pero ignora su resultado**
- Línea 263: `let optResult := optimizeReduction fc hw` — corre el e-graph
- Líneas 265-268: genera C con Solinas hardcodeado, ignora `optResult.optimizedExpr`
- El resultado del e-graph solo aparece en un comentario decorativo
- **Fix**: dispatch en `optResult.strategyName` para seleccionar reducción (~80 LOC)

**Bug 1.4: Tres paths de codegen verificado, NINGUNO usado por benchmarks**
- `emitPlanBasedNTTC` — usa selectBestPlan + emitCFromPlan
- `emitPerStageNTT` — usa mkPerStagePlan con reducción heterogénea
- `emitVerifiedNTTCFn` — usa Trust-Lean Path A
- Los tres funcionan. Los tres son dead code para benchmarks.

**Bug 7.2: emitPerStageNTT nunca se llama**
- Produce NTT heterogéneo (18 lazy + 2 Solinas para BabyBear)
- Implementado correctamente en NTTPlanCodeGen.lean:150
- Nunca llamado desde Bench.lean ni OptimizedNTTPipeline

### ALTOS (dejan performance en la mesa)

**Bug 4.1: costReport nunca compara Harvey**
- Línea 404-405: `if fc.isMersenne then ... else if solCost ≤ montyCost then "Solinas"...`
- Harvey=3 ciclos NUNCA se evalúa como candidato a ganador
- Para BabyBear scalar: Harvey(3) < Solinas(6) < Montgomery(7) — Harvey debería ganar
- **Fix**: agregar `harCost ≤ solCost` al condicional (~15 LOC)

**Bug 5.1: SIMD codegen ignora cost model — siempre usa Solinas**
- `lowerDIFButterflyVecStmt` siempre llama `lowerDIFButterflyStmt` (Solinas)
- En NEON, Solinas requiere u32→u64 widening (8 ciclos de penalty)
- Montgomery se queda en u32 lanes (0 widening penalty)
- Costo real NEON: Solinas=14 vs Montgomery=7 — **Montgomery es 2x más rápido en SIMD**
- **Fix**: consultar `selectReductionForBound` con hwIsSimd=true (~120 LOC)

**Bug 6.1: Bench.lean ignora HardwareCost para generación de código**
- `hw := hwFromString cfg.hardware` se crea correctamente
- Se pasa a `explainStrategy` (para printout informativo)
- `genNTTBenchC` NO recibe hw — genera el mismo C para ARM/x86/RISC-V
- **Fix**: pasar hw a genOptimizedBenchC (~30 LOC)

**Bug 3.1: Poseidon S-box sin reducción intermedia**
- `genSbox5Stmt`: x^5 = x*x * (x*x) * x — sin `% p` entre multiplicaciones
- Para Goldilocks: x^2 cabe en u128, pero x^4 = x^2 * x^2 ≈ 2^128 — overflow
- **Fix**: agregar reduce entre squarings, seleccionada por bound analysis (~80 LOC)

### MODERADOS (costos ocultos)

**Bug 4.3: costReport usa modelo distinto al e-graph**
- costReport: `pseudoMersenneFoldCost` (fórmula simple, sin wideningPenalty)
- E-graph: `mixedOpCost` (incluye wideningPenalty, cachePenalty)
- Resultado: costReport dice "Solinas wins" para NEON, e-graph dice "Montgomery wins"
- **Fix**: usar `mixedOpCost` en costReport (~20 LOC)

**Bug 8.1: E-graph satura con alternativas estrechas**
- `guidedOptimizeMixedF` Phase 3 solo agrega Harvey-para-add/sub
- `reductionAlternativeRules` (que agrega Montgomery/Barrett general) NO se pasa
- Montgomery como alternativa general para `reduce(mul(x,y))` no se explora
- **Fix**: pasar `reductionAlternativeRules p` como `extraRules` (~10 LOC)

**Bug 1.3: optimizeNTTWithBounds ignora estado del e-graph**
- Corre saturación pero `nttStageBoundAnalysis` solo lee NTTBoundConfig estático
- El DAG de relaciones con bounds tighter por e-class se descarta
- **Fix**: extraer bounds de s'.relations o eliminar dead code (~10-60 LOC)

**Bug 2.1: FRI fold sin bound analysis**
- `friFoldLoopStmt`: `output[i] = input[2i] + alpha * input[2i+1]` — sin reducción
- No hay `friFoldBoundAnalysis`
- **Fix**: crear análogo a nttStageBoundAnalysis para FRI (~100 LOC)

**Bug 7.3: emitCFromPlan genera C incompleto**
- Llama `data_load`, `cond_sub`, `monty_redc` sin proveer implementaciones
- C generado no compila standalone
- **Fix**: emitir preamble con helper functions (~60 LOC)

## Impacto Cuantificado

### Performance dejada en la mesa (BabyBear NTT 2^22, ARM scalar)

| Optimización no usada | Ciclos ahorrados/butterfly | Stages afectados | Speedup |
|----------------------|---------------------------|------------------|---------|
| Lazy reduction (18 stages) | 6 ciclos/bf × 18 stages | 18/20 | **~2.7x** |
| Harvey para stages con bound ≤ 2 | 3 ciclos (vs 6 Solinas) | últimos 2 | ~1.05x |
| **Total escalar** | | | **~2.8x** |

### Performance dejada en la mesa (BabyBear NTT 2^22, ARM NEON)

| Optimización no usada | Impacto |
|----------------------|---------|
| Montgomery en NEON (vs Solinas con widening) | **~2x** |
| + Lazy reduction (18 stages) | **~2.7x** adicional |
| **Total NEON** | **~5.4x** |

### Benchmark actual vs potencial (BabyBear 2^22 C)

| Config | Actual | Potencial | Ratio |
|--------|--------|-----------|-------|
| Scalar, Solinas every stage | 82ms | — | 1x |
| Scalar, 18 lazy + 2 Solinas | — | ~30ms | **2.7x** |
| NEON, Montgomery + lazy | — | ~6ms | **14x** |
| Plonky3 scalar Montgomery | 86ms | — | — |

## Causa Raíz

**Un solo bug causa el 80% del problema**: `Bench.lean` no importa ni usa el pipeline de optimización. Todo lo demás es consecuencia.

## Archivos a Modificar (Priority Order)

| # | Archivo | Bug | LOC |
|---|---------|-----|-----|
| 1 | `Bench.lean` | 1.1 + 6.1 | 50 |
| 2 | `OptimizedNTTPipeline.lean` | 1.2 + 4.1 + 4.3 | 115 |
| 3 | `MixedRunner.lean` | 8.1 | 10 |
| 4 | `VerifiedSIMDCodeGen.lean` | 5.1 | 120 |
| 5 | `NTTPlanCodeGen.lean` | 7.3 | 60 |
| 6 | `VerifiedProductionCodegen.lean` | 3.1 | 80 |
| 7 | `CrossRelNTT.lean` | 2.1 | 100 |
| **Total** | | **18 bugs** | **~535 LOC** |

## Lecciones

1. **Código que "funciona" no es código que "se usa"**: 5 días construyendo generadores verificados que nunca se conectaron al benchmarker
2. **Hardcoded strings matan optimizadores**: un `genNTTBenchC` con strings literales invalidó TODO el pipeline de e-graph + bounds + cost model
3. **Test end-to-end antes de celebrar**: deberíamos haber corrido `nttStageBoundAnalysis` → code emission → compile → benchmark el primer día
4. **El cost model que no drive code selection es decoración**: `costReport` es printf, no control flow

---

## FIX SPECS EXACTOS — Para el agente que implementa los arreglos

### Orden de aplicación (los fixes tienen dependencias)

```
Fix 1 (imports Bench.lean) → Fix 2 (FieldData→FieldConfig) → Fix 3 (wire hw a codegen)
Fix 4 (extraRules al e-graph) — independiente
Fix 5 (costReport Harvey) — independiente
Fix 6 (optimizedNTTC usa resultado del e-graph) — depende de Fix 4
Fix 7 (per-stage NTT en benchmarker) — depende de Fix 3
Fix 8 (SIMD cost-driven) — independiente
Fix 9 (Poseidon intermediate reduce) — independiente
```

### Fix 1: Bench.lean — Agregar imports del pipeline

**Archivo**: `Bench.lean`
**Líneas**: 16-20 (sección de imports)
**Código actual**:
```lean
import AmoLean.EGraph.Verified.Bitwise.CostModelDef
import AmoLean.EGraph.Verified.Bitwise.VerifiedCodeGen
```
**Código nuevo** (agregar DESPUÉS de las líneas existentes):
```lean
import AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline
import AmoLean.EGraph.Verified.Bitwise.CrossRelNTT
import AmoLean.EGraph.Verified.Bitwise.NTTPlanCodeGen
```
**Open adicional**:
```lean
open AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline (FieldConfig optimizedNTTC genOptimizedBenchC costReport babybearConfig koalabearConfig mersenne31Config goldilocksConfig)
open AmoLean.EGraph.Verified.Bitwise.CrossRelNTT (nttStageBoundAnalysis NTTBoundConfig)
```
**Verificación**: `lake env lean Bench.lean 2>&1 | grep error | head -3` — debe compilar sin errores nuevos

### Fix 2: Bench.lean — Conversión FieldData → FieldConfig

**Archivo**: `Bench.lean`
**Dónde insertar**: Después de la definición de `FieldData` (~línea 81)
**Código nuevo**:
```lean
/-- Convert Bench FieldData to pipeline FieldConfig. -/
def fieldDataToConfig (fd : FieldData) : FieldConfig :=
  if fd.pNat == 2013265921 then babybearConfig
  else if fd.pNat == 2130706433 then koalabearConfig
  else if fd.pNat == 2147483647 then mersenne31Config
  else if fd.pNat == 18446744069414584321 then goldilocksConfig
  else babybearConfig  -- fallback
```
**Verificación**: `#eval (fieldDataToConfig babybearFD).name` debe dar `"BabyBear"`

### Fix 3: Bench.lean — runOneBenchC pasa hw a codegen

**Archivo**: `Bench.lean`
**Líneas**: 558-559
**Código actual**:
```lean
  let code := match prim with
    | .ntt => genNTTBenchC fd logN iters
```
**Código nuevo**:
```lean
  let fc := fieldDataToConfig fd
  let code := match prim with
    | .ntt => genOptimizedBenchC fc logN iters hw
```
**NOTA**: `genOptimizedBenchC` debe existir en `OptimizedNTTPipeline.lean` con signature `(fc : FieldConfig) (logN iters : Nat) (hw : HardwareCost) → String`. Si no existe con esta signature exacta, el agente debe crearla o adaptar `optimizedNTTC` para que sirva como benchmark. Lo importante es que la función:
1. Reciba `HardwareCost`
2. Llame al e-graph con `reductionAlternativeRules` (Fix 4)
3. Use `nttStageBoundAnalysis` para selección per-stage
4. Genere C que compile con `cc -O2` y produzca output CSV `amo_us,p3_us,melem,diff%`

**Aplicar el mismo cambio en líneas 714-718** (el segundo dispatch de codegen en el main loop).

**Verificación**: `lake env lean --run Bench.lean -- --field babybear --size 20 --primitive ntt --lang c --hardware arm-scalar` debe producir resultados con la reducción optimizada (lazy en stages tempranos).

### Fix 4: MixedRunner.lean — Pasar reductionAlternativeRules al e-graph

**Archivo**: `AmoLean/EGraph/Verified/Bitwise/MixedRunner.lean`
**NO modificar** — este archivo está bien. El fix va en el CALLER.

**Archivo**: `AmoLean/EGraph/Verified/Bitwise/OptimizedNTTPipeline.lean`
**Líneas**: ~150 (dentro de `optimizeReduction`)
**Código actual**:
```lean
  match guidedOptimizeMixedF fc.pNat hw cfg seed with
```
**Código nuevo**:
```lean
  -- Import at top of file:
  -- import AmoLean.EGraph.Verified.Bitwise.ReductionAlternativeRules
  -- open ... (reductionAlternativeRules)

  match guidedOptimizeMixedF fc.pNat hw cfg seed (extraRules := reductionAlternativeRules fc.pNat) with
```
**Efecto**: El e-graph ahora explora Montgomery, Barrett, y Harvey como alternativas para `reduce(x)`. La extracción cost-aware (`multiCandidateExtract`) selecciona la más barata para el hardware target.

**Verificación**: `optimizeReduction babybearConfig arm_neon_simd` debe retornar `strategyName = "Montgomery REDC"` (porque Montgomery es más barato en NEON).

### Fix 5: OptimizedNTTPipeline.lean — costReport incluye Harvey en winner

**Archivo**: `AmoLean/EGraph/Verified/Bitwise/OptimizedNTTPipeline.lean`
**Líneas**: 404-405
**Código actual**:
```lean
    let winner := if fc.isMersenne then "Mersenne fold"
      else if solCost ≤ montyCost then "Solinas fold" else "Montgomery REDC"
```
**Código nuevo**:
```lean
    let minCost := Nat.min solCost (Nat.min montyCost harCost)
    let winner := if fc.isMersenne then "Mersenne fold"
      else if minCost == harCost then "Harvey cond-sub"
      else if minCost == solCost then "Solinas fold"
      else "Montgomery REDC"
```
**NOTA**: Harvey solo es válido cuando el input tiene bound ≤ 2. El winner debería tener una nota: `"Harvey cond-sub (requires bounded input)"`. El agente debe decidir si reportar Harvey como ganador genérico (puede ser misleading) o reportar Harvey con la nota de precondición.

**Verificación**: `costReport babybearConfig` debe mostrar `"Harvey cond-sub"` para ARM scalar (Harvey=3 < Solinas=6).

### Fix 6: OptimizedNTTPipeline.lean — optimizedNTTC usa el resultado del e-graph

**Archivo**: `AmoLean/EGraph/Verified/Bitwise/OptimizedNTTPipeline.lean`
**Líneas**: 259-332 (reescribir `optimizedNTTC`)
**Problema**: Las líneas 265-272 emiten C hardcodeado ignorando `optResult`
**Fix**: Reemplazar la generación hardcodeada con una que use `optResult.strategyName` para dispatch:

```lean
def optimizedNTTC (fc : FieldConfig) (hw : HardwareCost) (logN iters : Nat) ... : String :=
  let optResult := optimizeReduction fc hw cfg
  -- Usar el resultado del e-graph para generar la función de reducción correcta
  let reduceCode := match optResult.strategyName with
    | "Solinas fold" => genSolinasReduceC fc
    | "Montgomery REDC" => genMontyReduceC fc
    | "Harvey conditional subtraction" => genHarveyReduceC fc
    | _ => genSolinasReduceC fc  -- fallback
  -- Usar bound analysis para NTT per-stage
  let boundCfg : NTTBoundConfig := {
    numStages := logN, prime := fc.pNat,
    hwIsSimd := hw.isSimd, arrayIsLarge := 2^logN > 4096
  }
  let stageAnalysis := nttStageBoundAnalysis boundCfg
  -- Generar NTT loop con reducción per-stage
  ...
```

**Este es el fix más complejo** (~80 LOC). El agente debe:
1. Generar la función `amo_reduce` basada en `optResult.strategyName`
2. Generar la función `amo_bf` (butterfly) que use `amo_reduce` (o NO la use si el stage es lazy)
3. Generar el NTT loop donde los stages tempranos NO llaman `amo_reduce` (lazy) y los últimos sí
4. Mantener la función `p3_bf` (Plonky3 Montgomery) como referencia
5. Mantener el timing harness

**Verificación**: `genOptimizedBenchC babybearConfig 20 10 arm_cortex_a76` debe generar C donde stages 0-17 son lazy y 18-19 usan Solinas. El C debe compilar con `cc -O2` y producir output CSV.

### Fix 7: Bench.lean — Usar per-stage NTT del pipeline

**Depende de**: Fix 3 + Fix 6
**Archivo**: `Bench.lean` o `OptimizedNTTPipeline.lean`
**Acción**: Asegurar que `genOptimizedBenchC` genera un NTT loop heterogéneo (no uniforme). Esto puede requerir:

1. Dentro de `genOptimizedBenchC`, generar N funciones butterfly:
   - `amo_bf_lazy(a, b, w)` — sin reducción: `sum = a + w*b; diff = p + a - w*b`
   - `amo_bf_solinas(a, b, w)` — con Solinas fold
   - `amo_bf_harvey(a, b, w)` — con Harvey conditional sub

2. En el NTT loop, hacer dispatch por stage:
   ```c
   for (int st = 0; st < logn; st++) {
     void (*bf)(uint32_t*, uint32_t*, uint32_t);
     if (st < 18) bf = amo_bf_lazy;
     else bf = amo_bf_solinas;
     for (int g = 0; ...) for (int p = 0; ...) bf(&d[i], &d[j], tw[...]);
   }
   ```

**Verificación**: El benchmark debe mostrar que AMO-Lean con lazy reduction es significativamente más rápido que la versión uniforme. BabyBear 2^22 escalar debería bajar de ~82ms a ~30-35ms.

### Fix 8: VerifiedSIMDCodeGen.lean — SIMD butterfly acepta ReductionChoice

**Archivo**: `AmoLean/EGraph/Verified/Bitwise/VerifiedSIMDCodeGen.lean`
**Líneas**: 350-359
**Código actual**: `lowerDIFButterflyVecStmt` hardcodea Solinas
**Código nuevo**: Agregar parámetro `ReductionChoice` o `useMontgomery : Bool`:

```lean
def lowerDIFButterflyVecStmt (p k c : Nat) (lanes : Nat)
    (useMontgomery : Bool := false) (mu : Nat := 0) : VecStmt :=
  if useMontgomery then
    -- Usar lowerMontyReduceVecStmt para el butterfly
    let scalarBody := ... -- Montgomery butterfly body
    ...
  else
    -- Actual code (Solinas fold)
    let (scalarBody, sumVar, bPrimeVar, _) := lowerDIFButterflyStmt ...
    ...
```

**Verificación**: `emitNTTSIMD_C 20 2013265921 27 134217727 neonConfig` con Montgomery debe producir C NEON sin widening penalty.

### Fix 9: VerifiedProductionCodegen.lean — Poseidon S-box con reducciones intermedias

**Archivo**: `AmoLean/Bridge/VerifiedProductionCodegen.lean`
**Líneas**: 205-213 (`genSbox5Stmt`)
**Código actual**: 3 multiplicaciones sin reducción intermedia
**Código nuevo**: Insertar `reduce(x2)` después de cada squaring:

```lean
def genSbox5StmtWithReduce (xVar : VarName) (p k c : Nat) (cgs : CodeGenState) :
    Stmt × VarName × CodeGenState :=
  let (x2Var, cgs1) := cgs.freshVar
  let s1 := Stmt.assign x2Var (.binOp .mul (.varRef xVar) (.varRef xVar))
  -- Reduce x2 to [0, 2p) via Solinas fold
  let x2Reduced := solinasFoldLLE (.varRef x2Var) k c
  let (x2rVar, cgs2) := cgs1.freshVar
  let s1r := Stmt.seq s1 (Stmt.assign x2rVar x2Reduced)
  -- x4 = x2r * x2r (bounded: < (2p)^2 = 4p^2, fits in u64 for 31-bit primes)
  let (x4Var, cgs3) := cgs2.freshVar
  let s2 := Stmt.assign x4Var (.binOp .mul (.varRef x2rVar) (.varRef x2rVar))
  -- x5 = x4 * x (bounded: < 4p^3, may need reduction for Goldilocks)
  let (x5Var, cgs4) := cgs3.freshVar
  let s3 := Stmt.assign x5Var (.binOp .mul (.varRef x4Var) (.varRef xVar))
  (Stmt.seq s1r (Stmt.seq s2 s3), x5Var, cgs4)
```

**NOTA**: Para 31-bit primes, x2 < p² < 2⁶² → Solinas fold produce < 2p < 2³². x4 < (2p)² < 2⁶⁴ → cabe en u64. x5 < 2⁶⁴ × p < 2⁹⁵ → cabe en u128. Para Goldilocks: x2 < p² < 2¹²⁸ → necesita reduce. x4 sin reduce overflows u128.

**Verificación**: `genSbox5StmtWithReduce (.user "x") 2013265921 27 134217727 {}` debe producir Stmt con 5 operaciones (3 muls + 2 reduces).

## Cómo verificar que TODOS los fixes están aplicados

Después de aplicar todos los fixes, correr:

```bash
# 1. Compilar
lake build 2>&1 | tail -3
# Esperar: "Build completed successfully"

# 2. Verificar 0 sorry
grep -rn "sorry" AmoLean/EGraph/Verified/Bitwise/OptimizedNTTPipeline.lean AmoLean/Bridge/VerifiedProductionCodegen.lean | grep -v "^.*:.*--"
# Esperar: vacío

# 3. Bound analysis funciona end-to-end
lake env lean --run Bench.lean -- --field babybear --size 20 --primitive ntt --lang c --hardware arm-scalar --explain 2>&1 | grep -E "Stage|lazy|Harvey|Solinas|Strategy"
# Esperar: "18 lazy + 2 Solinas" en el explain, código C con dispatch per-stage

# 4. Benchmark real
lake env lean --run Bench.lean -- --field babybear --size 22 --primitive ntt --lang c --hardware arm-scalar 2>&1 | grep "BabyBear"
# Esperar: AMO ~30-35ms (vs ~82ms antes del fix), diff vs P3 > +50%

# 5. SIMD benchmark
lake env lean --run Bench.lean -- --field babybear --size 22 --primitive ntt --lang c --hardware arm-neon 2>&1 | grep "BabyBear"
# Esperar: AMO con Montgomery NEON, diferente de scalar
```

---

## FIXES FALTANTES (Bugs sin fix spec en la sección anterior)

### Fix 10: Bug 1.3 — optimizeNTTWithBounds corre e-graph que nadie consume

**Archivo**: `AmoLean/EGraph/Verified/Bitwise/BoundIntegration.lean`
**Líneas**: 61-76 (`optimizeNTTWithBounds`)
**Problema**: Corre saturación del e-graph multi-relacional, produce estado `s'` con DAG de bounds. Luego llama `nttStageBoundAnalysis` que NO lee `s'` — usa solo NTTBoundConfig estático. El e-graph es dead code.
**Decisión**: Hay dos opciones. Opción A: extraer bounds de `s'.relations` y alimentar `nttStageBoundAnalysis`. Opción B (pragmática): eliminar la saturación y usar solo `nttStageBoundAnalysis` directo — que es lo que ya funciona correctamente.

**Acción** (Opción B — eliminar dead code):
En cualquier función que llame `optimizeNTTWithBounds`, reemplazar con llamada directa a `nttStageBoundAnalysis`:
```lean
-- ANTES:
let (state, schedule) := optimizeNTTWithBounds g rules p numStages hwIsSimd
-- DESPUÉS:
let cfg : NTTBoundConfig := { numStages := numStages, prime := p, hwIsSimd := hwIsSimd }
let schedule := nttStageBoundAnalysis cfg
```
**LOC**: ~10
**Verificación**: Buscar todos los callers de `optimizeNTTWithBounds` con `grep -rn "optimizeNTTWithBounds" --include="*.lean"` y reemplazar.

### Fix 11: Bug 2.1 — FRI fold sin bound analysis

**Archivo**: `AmoLean/EGraph/Verified/Bitwise/CrossRelNTT.lean` (agregar)
**Archivo**: `AmoLean/Bridge/VerifiedProductionCodegen.lean` (modificar `friFoldLoopStmt`)
**Problema**: FRI fold calcula `output[i] = input[2i] + alpha * input[2i+1]` sin reducción. El producto `alpha * b` puede exceder el rango del campo. No hay análisis de bounds para FRI.

**Código nuevo en CrossRelNTT.lean** (agregar después de `nttStageBoundAnalysis`):
```lean
/-- FRI fold bound analysis: after alpha * b, the result is < p * p.
    After add (a + alpha*b), result is < p + p*p = p(1+p).
    Need to reduce if p(1+p) > word_max.
    For 31-bit primes: p(1+p) < 2^31 * 2^31 = 2^62 < 2^64. Fits in u64.
    For Goldilocks: p(1+p) ≈ 2^128. Needs u128 and reduction after mul. -/
def friFoldReductionChoice (p : Nat) (bitwidth : Nat := 64) : ReductionChoice :=
  if p * (1 + p) < 2^bitwidth then .lazy  -- no reduction needed
  else .solinasFold  -- need to reduce after mul
```

**Código modificado en VerifiedProductionCodegen.lean** — `friFoldLoopStmt`:
El body actual es:
```lean
(Stmt.assign (.user "result") (.binOp .add (.varRef (.user "a"))
  (.binOp .mul (.varRef (.user "alpha")) (.varRef (.user "b")))))
```
Para Goldilocks, agregar reduce después del mul:
```lean
let mulExpr := .binOp .mul (.varRef (.user "alpha")) (.varRef (.user "b"))
let body := if friFoldReductionChoice p > 64 then
  -- Need intermediate reduction for Goldilocks
  Stmt.seq
    (Stmt.assign (.user "ab") mulExpr)
    (Stmt.seq (Stmt.assign (.user "ab_r") (solinasFoldLLE (.varRef (.user "ab")) k c))
    (Stmt.assign (.user "result") (.binOp .add (.varRef (.user "a")) (.varRef (.user "ab_r")))))
else
  -- 31-bit primes: no reduction needed, fits in u64
  Stmt.assign (.user "result") (.binOp .add (.varRef (.user "a")) mulExpr)
```
**LOC**: ~40
**Verificación**: Para Goldilocks, `friFoldReductionChoice goldilocksP` debe dar `.solinasFold`. Para BabyBear, `.lazy`.

### Fix 12: Bug 4.3 — costReport usa modelo distinto al e-graph

**Archivo**: `AmoLean/EGraph/Verified/Bitwise/OptimizedNTTPipeline.lean`
**Líneas**: 400-406 (`costReport`)
**Problema**: Usa `pseudoMersenneFoldCost` (sin wideningPenalty) mientras el e-graph usa `mixedOpCost` (con wideningPenalty). Para NEON: costReport dice Solinas=6, e-graph dice Solinas=14.
**Fix**: Importar y usar `mixedOpCost` en vez de las funciones standalone:

```lean
-- Agregar import:
open AmoLean.EGraph.Verified.Bitwise.CostExtraction (mixedOpCost)
-- o la función correcta que computa el costo con penalties

-- En costReport, reemplazar:
let solCost := pseudoMersenneFoldCost hw
let montyCost := montgomeryCost hw
-- Con:
let solCost := mixedOpCost hw (.reduceGate 0 fc.pNat)  -- o el MixedNodeOp correcto para Solinas
let montyCost := mixedOpCost hw (.montyReduce 0 fc.pNat fc.muNat)
let harCost := mixedOpCost hw (.harveyReduce 0 fc.pNat)
```

**NOTA**: El agente debe verificar la signature de `mixedOpCost` — puede tomar `MixedNodeOp` directamente o puede necesitar un wrapper. Buscar con `grep -rn "def mixedOpCost" --include="*.lean"`.
**LOC**: ~20
**Verificación**: `costReport babybearConfig` para ARM NEON debe mostrar Solinas=14 (no 6).

### Fix 13: Bug 7.3 — emitCFromPlan genera C incompleto

**Archivo**: `AmoLean/EGraph/Verified/Bitwise/NTTPlanCodeGen.lean`
**Líneas**: 109-113 (`emitCFromPlan`)
**Problema**: El C generado llama `data_load(i)`, `cond_sub(x, p)`, `monty_redc(x, p, mu)` sin proveer definiciones. No compila.
**Fix**: Agregar preamble con helper function definitions:

```lean
def emitHelperPreamble (p mu : Nat) (elemType : String := "uint32_t") : String :=
  s!"static inline {elemType} cond_sub({elemType} x, {elemType} p) \{
    return (x >= p) ? x - p : x;
}
static inline {elemType} solinas_fold({elemType} x, int k, {elemType} c) \{
    return ((x >> k) * c) + (x & ((1u << k) - 1));
}
static inline {elemType} monty_redc({elemType} x, {elemType} p, {elemType} mu) \{
    {elemType} m = (x * mu) & 0xFFFFFFFF;
    uint64_t s = (uint64_t)x + (uint64_t)m * p;
    {elemType} q = (uint32_t)(s >> 32);
    return (q >= p) ? q - p : q;
}
#define data_load(arr, i) (arr[i])
#define data_store(arr, i, v) (arr[i] = (v))
"

-- Modificar emitCFromPlan:
def emitCFromPlan (plan : Plan) (funcName : String) : String :=
  let preamble := emitHelperPreamble plan.field 0  -- mu needs to come from plan
  let body := lowerNTTFromPlan plan
  preamble ++ "\n" ++ ... -- existing code
```

**También**: Fix el hardcoded `uint32_t*` en la signature (línea 111) — debe ser `uint64_t*` para Goldilocks:
```lean
  let elemType := if plan.field > 2^32 then "uint64_t" else "uint32_t"
  let header := s!"void {funcName}({elemType}* data, const {elemType}* twiddles, size_t n) \{\n"
```
**LOC**: ~60
**Verificación**: `emitCFromPlan (mkPerStagePlan 2013265921 1024) "test_ntt"` debe producir C que compile con `cc -O2 -c`.

### Fix 14: Bug 18 — Dos paths paralelos de decisión per-stage con lógica distinta

**Archivos**: `CrossRelNTT.lean` y `Discovery/StageContext.lean`
**Problema**: Existen dos funciones que deciden la reducción per-stage:
1. `selectReductionForBound` (CrossRelNTT.lean:39) — usa `boundK ≤ 2 → Harvey`
2. `reductionDecision` (StageContext.lean:53) — NUNCA retorna Harvey

Estas dan resultados distintos para el mismo input. `mkPerStagePlan` usa `reductionDecision`, `nttStageBoundAnalysis` usa `selectReductionForBound`.

**Fix**: Unificar en una sola función. La lógica correcta es la de `selectReductionForBound` (que sí considera Harvey). Modificar `reductionDecision` en StageContext.lean:

**Archivo**: `AmoLean/EGraph/Verified/Bitwise/Discovery/StageContext.lean`
**Líneas**: 53-60
**Código actual**:
```lean
def reductionDecision (ctx : StageContext) : ReductionChoice :=
  if ctx.stageIndex + 1 = ctx.totalStages then .solinasFold
  else if (ctx.inputBoundK + 1) * ctx.prime < 2 ^ ctx.bitwidth then .lazy
  else if ctx.hwIsSimd then .montgomery
  else .solinasFold
```
**Código nuevo**:
```lean
def reductionDecision (ctx : StageContext) : ReductionChoice :=
  if ctx.stageIndex + 1 = ctx.totalStages then
    -- Last stage: must produce canonical [0, p) output
    .solinasFold
  else if (ctx.inputBoundK + 1) * ctx.prime < 2 ^ ctx.bitwidth then
    -- Bounds fit in word width: skip reduction entirely
    .lazy
  else if ctx.inputBoundK ≤ 2 then
    -- Small bounds after previous reduction: Harvey is cheapest (3 cycles)
    .harvey
  else if ctx.hwIsSimd then
    -- SIMD: Montgomery stays in u32 lanes (no widening penalty)
    .montgomery
  else
    -- Default scalar: Solinas fold
    .solinasFold
```
**LOC**: ~5 (modify existing function)
**Verificación**: `reductionDecision { stageIndex := 18, totalStages := 20, inputBoundK := 2, ... }` debe dar `.harvey` (no `.solinasFold`).

---

## FIX CENTRAL: Lazy Reduction en el Benchmarker (el hallazgo original)

Este es el fix que detonó toda la auditoría. Los fixes 1-7 lo habilitan, pero ninguno especifica el **código C exacto** que implementa lazy reduction en el NTT benchmark. Aquí está.

### El butterfly lazy vs butterfly con reducción

**Archivo**: `AmoLean/EGraph/Verified/Bitwise/OptimizedNTTPipeline.lean`
**Función**: `genOptimizedBenchC` (o `optimizedNTTC`)

El C generado necesita DOS funciones butterfly:

```c
// Butterfly SIN reducción (lazy): para stages 0-17
// Input: a, b en [0, K*p) donde K crece con cada stage
// Output: sum, diff en [0, (K+1)*p)
// Costo: 1 mul + 1 add + 1 sub = 3 ciclos
static inline void amo_bf_lazy(uint32_t *a, uint32_t *b, uint32_t w) {
    uint64_t wb = (uint64_t)w * (*b);  // widening mul
    uint32_t wb32 = (uint32_t)wb;       // truncate to 32 bits (lazy: no reduce)
    uint32_t oa = *a;
    *a = oa + wb32;                      // sum (puede exceder p, OK por lazy)
    *b = oa - wb32 + P;                  // diff + P para evitar underflow
}

// Butterfly CON Solinas fold: para stages 18-19
// Input: a, b en [0, K*p)
// Output: sum, diff en [0, 2p) después del fold
// Costo: 1 mul + 1 add + 1 sub + 2 folds = 9 ciclos
static inline void amo_bf_reduce(uint32_t *a, uint32_t *b, uint32_t w) {
    uint64_t wb = (uint64_t)w * (*b);
    uint32_t wb_r = amo_reduce(wb);     // Solinas fold: [0, 2p)
    uint32_t oa = *a;
    uint32_t s = oa + wb_r;
    *a = amo_reduce(s);                  // fold sum
    *b = amo_reduce((uint64_t)P + oa - wb_r); // fold diff
}
```

Y el NTT loop con dispatch per-stage:

```c
// NTT loop con lazy reduction per-stage
// schedule[] = array de 0/1: 0=lazy, 1=reduce
int schedule[LOGN];  // pre-computed from nttStageBoundAnalysis
for (int s = 0; s < LOGN - 2; s++) schedule[s] = 0; // lazy
schedule[LOGN-2] = 1; schedule[LOGN-1] = 1;          // reduce

for (size_t st = 0; st < logn; st++) {
    size_t h = 1 << (logn - st - 1);
    void (*bf)(uint32_t*, uint32_t*, uint32_t) =
        schedule[st] ? amo_bf_reduce : amo_bf_lazy;
    for (size_t g = 0; g < (1u << st); g++)
        for (size_t p = 0; p < h; p++) {
            size_t i = g * 2 * h + p, j = i + h;
            bf(&d[i], &d[j], tw[(st*(n/2)+g*h+p) % tw_sz]);
        }
}
```

### Cómo generar este C desde Lean

En `OptimizedNTTPipeline.lean`, la función `genOptimizedBenchC` debe:

1. Llamar `nttStageBoundAnalysis` para obtener el schedule:
```lean
let cfg : NTTBoundConfig := { numStages := logN, prime := fc.pNat, hwIsSimd := hw.isSimd }
let analysis := nttStageBoundAnalysis cfg
```

2. Generar el array `schedule[]` desde `analysis`:
```lean
let scheduleInit := analysis.map fun (stage, red, _) =>
  match red with | .lazy => "0" | _ => "1"
let scheduleC := s!"int schedule[{logN}] = \{{String.intercalate "," scheduleInit}};"
```

3. Emitir ambas butterfly functions + el NTT loop con dispatch.

4. Para Plonky3 reference: mantener el butterfly Montgomery uniforme (sin lazy).

### Verificación del fix central

```bash
# Generar el C optimizado y verificar que tiene lazy
lake env lean --run Bench.lean -- --field babybear --size 22 --primitive ntt --lang c --hardware arm-scalar --explain 2>&1 | grep -E "lazy|Harvey|Solinas"
# Debe mostrar: "18 lazy, 2 Solinas"

# Compilar y ejecutar
lake env lean --run Bench.lean -- --field babybear --size 22 --primitive ntt --lang c --hardware arm-scalar 2>&1 | grep "BabyBear"
# ANTES del fix: BabyBear 2^22 C ~82ms (Solinas every stage)
# DESPUÉS del fix: BabyBear 2^22 C ~30-35ms (18 lazy + 2 Solinas)
# Diff vs Plonky3: +50-60% (vs +4% antes)
```

### Por qué el speedup es ~2.7x

- 20 stages × N/2 butterflies por stage
- Antes: cada butterfly cuesta 9 ciclos (mul + add + sub + 2 folds)
- Después: 18 stages × 3 ciclos + 2 stages × 9 ciclos = 54 + 18 = 72 ciclos totales por elemento
- Antes: 20 × 9 = 180 ciclos totales por elemento
- Ratio: 180 / 72 = **2.5x**
- Con el beneficio adicional de menos presión en instruction cache (lazy butterfly es más pequeño): **~2.7x**

---

## Tabla final: TODOS los bugs → TODOS los fixes

| Bug | Fix # | Status |
|-----|-------|--------|
| 1.1 Bench.lean bypassa pipeline | Fix 1 | ✓ especificado |
| 1.2 optimizedNTTC ignora e-graph | Fix 6 | ✓ especificado |
| 1.3 optimizeNTTWithBounds dead code | Fix 10 | ✓ especificado |
| 1.4 Tres codegen paths unused | Fix 1+3 | ✓ especificado |
| 2.1 FRI fold sin bounds | Fix 11 | ✓ especificado |
| 3.1 Poseidon sin reduce intermedio | Fix 9 | ✓ especificado |
| 4.1 costReport no compara Harvey | Fix 5 | ✓ especificado |
| 4.3 costReport modelo inconsistente | Fix 12 | ✓ especificado |
| 5.1 SIMD ignora cost model | Fix 8 | ✓ especificado |
| 5.2 selectReductionForBound varado | Fix 8 | ✓ cubierto |
| 6.1 Bench.lean ignora hw | Fix 3 | ✓ especificado |
| 6.2 NEON gets Solinas | Fix 3+8 | ✓ cubierto |
| 6.3 AVX2 gets same as scalar | Fix 3+8 | ✓ cubierto |
| 7.2 emitPerStageNTT unused | Fix 7 | ✓ especificado |
| 7.3 emitCFromPlan C incompleto | Fix 13 | ✓ especificado |
| 8.1 E-graph alternativas estrechas | Fix 4 | ✓ especificado |
| 8.3 optimizeReduction devuelve seed | Fix 4 | ✓ cubierto |
| 18 Dos paths per-stage con lógica distinta | Fix 14 | ✓ especificado |
| **CENTRAL: Lazy reduction no usado** | Fix 6+7+Central | ✓ especificado con código C |

**18 bugs → 14 fixes + 1 fix central = 15 fix specs con código exacto. 0 bugs sin cobertura.**
