# TRZK v3.5.0 — REDC-Schedule: Plan Filosófico y Técnico

**Fecha**: 2026-04-07
**Branch**: fixes
**Prerequisito**: v3.4.0 (Harvey chaining) + v3.4.1 (SIMD-aware cost model)

---

## Tesis Central

Las optimizaciones NTT "artesanales" de la literatura (sqdmulh REDC, V0/V1 interleaving,
stage merging, negacyclic twist merge) no son trucos ad-hoc — son puntos en un espacio
de decisiones que nuestro `Plan/NTTStage` no explora hoy. La diferencia entre "artesanal"
y "sistemático" no es CUÁLES optimizaciones se aplican, sino SI el framework las descubre
automáticamente.

### Estado actual del espacio de decisiones

```
NTTStage = RadixChoice × ReductionChoice       (2 dimensiones)
Plan = NTTStage[] × NTTOrdering                 (structure + ordering)
```

### Espacio expandido propuesto

```
NTTStage = RadixChoice × ReductionChoice × REDCMethod × ILPFactor
Plan = NTTStage[] × BlockingConfig × TwiddleMode
```

Cada dimensión nueva convierte una optimización artesanal en una regla de equivalencia
que el e-graph descubre y el cost model evalúa:

| Optimización artesanal | Dimensión sistemática | Regla de equivalencia |
|------------------------|----------------------|----------------------|
| "Usar sqdmulh en NEON" | `REDCMethod.sqdmulhMontgomery` | `REDC_vmull(tw,b,p,μ) ≡ REDC_sqdmulh(tw,b,p,μ_tw)` |
| "Interleave 2 butterflies" | `ilpFactor := 2` | `loop(i, bf(d[i])) ≡ loop(i step 2, bf(d[i]); bf(d[i+1]))` |
| "Fusionar últimos 6 stages" | `blockingFrom := some 10` | `seq(S_L,...,S_N) ≡ BlockedStages(L,N,blockSize)` |
| "Absorber twist en twiddles" | `TwiddleMode.twistMerged` | `NTT(twist(d,g),ω) ≡ NTT(d,merge(ω,g))` |

---

## Por qué calibración empírica, no estimaciones teóricas

El cost model actual ya tiene un precedente de sobreestimación: `wideningPenalty=8`
para Solinas NEON produce un costo de 14 ciclos, pero el código real (vmulq_u32 en u32
sin widening) cuesta ~6. La diferencia no afectó la *dirección* de la selección (Harvey
seguía ganando) pero inflaba las *predicciones absolutas*.

Con 4 dimensiones nuevas, cada una con su propio modelo de costos (register spill, shuffle
overhead, V0/V1 occupancy, memory bandwidth), el riesgo de descalibración se multiplica.

**Solución**: implementar una dimensión, benchmarkear, calibrar, iterar. No implementar
4 dimensiones con costos teóricos y esperar que el modelo acierte.

---

## Hallazgo Crítico: El "P3 Reference" es un Strawman

`genP3ButterflyC` (OptimizedNTTPipeline.lean:279-285) genera:
```c
wb = ((uint64_t)w * (uint64_t)(*b)) % (uint64_t)p;  // naive % p
*a = (uint32_t)(((uint64_t)oa + wb) % (uint64_t)p);
```

Esto es módulo nativo (hardware UDIV), sin Montgomery, sin SIMD. **No es Plonky3.**
Nuestros "+64% vs P3" son contra esta referencia naive.

El shim real de Plonky3 (`verification/plonky3/`) solo exporta Goldilocks (64-bit).
Para comparar con P3 real en BabyBear, hay que extender el shim con `monty-31`.

**Acción**: B0 del plan incluye tanto documentar la limitación como extender el benchmark.

---

## Análisis por Dimensión

### Dimensión 1: REDCMethod (MAYOR IMPACTO)

**Actual**: vmull widening REDC — procesa 2 lanes de uint64x2_t, ~20+ instrucciones
**Objetivo**: sqdmulh Montgomery — procesa 4 lanes de int32x4_t, ~15 instrucciones

**Secuencia sqdmulh (7 instrucciones de REDC + canonicalización)**:
```asm
vqdmulhq_s32   c_hi, b, tw           // high of 2*b*tw
vmulq_s32       q, b, mu_tw          // b * (tw * mu mod 2^32), precomputable
vqdmulhq_s32   qp_hi, q, p_vec      // high of 2*q*p
vhsubq_s32      raw, c_hi, qp_hi    // (c_hi - qp_hi) / 2, raw ∈ (-p, p)
vcltq_s32       mask, raw, #0        // canonicalize: negative → add p
vandq_s32       fix, mask, p_vec
vaddq_s32       wb_red, raw, fix     // wb_red ∈ [0, p)
```

**Diseño clave**: signed arithmetic CONTENIDA dentro del REDC. Después de
canonicalización, `wb_red ∈ [0, p)` — sum/diff/Harvey siguen en unsigned como hoy.
Zero cambio en la butterfly exterior.

**Infraestructura existente (HUÉRFANA)**:
- `UnifiedCodeGen.lean:439-465` — emite la secuencia sqdmulh completa como string C
- `VerifiedSIMDCodeGen.lean:231` — `VecSpecialOp.satDoublingMulHigh` para vqdmulhq
- `InstructionScheduling.lean:214-260` — análisis de latencias y scheduling

**Precomputación necesaria**: `mu_tw[i] = tw[i] * mu mod 2^32` — una tabla adicional
del mismo tamaño que twiddles. Cabe en L1 cache junto con los twiddles.

**Gain estimado**: ~1.7× en instrucciones (26→15), ~2× en throughput (4 lanes vs 2 lanes).
Calibrar con benchmark real.

### Dimensión 2: ILPFactor (SEGUNDO IMPACTO)

**Actual**: 1 butterfly por iteración del inner loop. V1 idle ~60%.
**Objetivo**: 2 butterflies intercaladas. V0 ejecuta REDC de bf_B mientras V1 ejecuta
add/sub de bf_A.

**Implementación en emitter**: cambiar step del inner loop de `lanes` a `2*lanes`:
```c
for (pr = 0; pr < halfSize; pr += 2 * lanes) {
    neon_bf_dit_har(&data[i],       &data[j],       &tw[tw_idx],       ...);
    neon_bf_dit_har(&data[i+lanes], &data[j+lanes], &tw[tw_idx+lanes], ...);
}
```

**Register pressure**: 2 butterflies × ~20-22 registros = 40-44, exceede 32 NEON.
El compilador C spilla ~8-12 registros. Con sqdmulh (menos registros por REDC),
la presión baja a ~30-35 — más manejable.

**El compilador vs inline assembly**: con C intrinsics y `-O2`, el compilador de ARM
hace instruction scheduling automático. El ilpFactor=2 le da más oportunidades de
reordenar. No necesitamos assembly — el compilador hace el interleaving.

**Gain estimado**: 20-40% (papers). Calibrar con benchmark real.

### Dimensión 3: BlockingConfig (TERCER IMPACTO, diferir)

**Para N=2^16**: stages 10-15 (halfSize ≤ 32) pueden fusionarse en bloques
de 64 elementos (16 data registers + 16 para computación).

**Stages 10-13** (halfSize 32→4): butterflies entre registros, zero shuffles.
**Stages 14-15** (halfSize 2→1): intra-register, necesitan `trn_4x4` (~8 instrucciones
por grupo de 4 registros, ~64 totales amortizadas en ~192 butterflies).

**Gain**: 6× menos memory traffic para esos stages (~15-20% del NTT total).
**Complejidad**: Alta. Requiere nuevo emitter `emitBlockedStagesC`.
**Decisión**: Diferir hasta después de medir impacto de dimensiones 1+2.

### Dimensión 4: TwiddleMode (BAJO COSTO, GRATIS)

**TwiddleMode.twistMerged**: absorber pre-multiplicación negacyclic `g^i` en los
twiddles del primer stage. Solo cambia `_init_twiddles_real` — zero cambios en emitter.
Solo aplica si el NTT es negacyclic (Z_p[X]/(X^n+1)).

**Gain**: ~5-8% (elimina N multiplicaciones de preprocessing).

---

## Plan de Ejecución: 6 Bloques Incrementales

### B35-0: Benchmark Honesto (FUNDACIONAL, 1 día)

**Objetivo**: Establecer baseline real contra Plonky3 con monty-31 NEON.

**Tareas**:
1. Documentar en OptimizedNTTPipeline.lean:279-285 que `genP3ButterflyC` es naive scalar, no P3 real
2. Extender `verification/plonky3/plonky3_shim/src/lib.rs` para exportar monty-31 BabyBear NTT
   - Usar `p3_monty_31::MontyField31<BabyBearParameters>` de Plonky3
   - Exportar `plonky3_babybear_ntt_forward(data, len)` via C FFI
3. Escribir `verification/plonky3/benchmark_babybear.c` que compare AMO vs P3 real
4. Correr: BabyBear N=2^16 y 2^20, scalar y NEON
5. Registrar resultados como baseline en BENCHMARKS.md

**Archivos a leer**: `verification/plonky3/plonky3_shim/src/lib.rs`, `verification/plonky3/Makefile`
**Archivos a modificar**: `verification/plonky3/plonky3_shim/src/lib.rs`, `verification/plonky3/Makefile`, nuevo `benchmark_babybear.c`
**Gate**: benchmark compila y corre, produce números para ambos

### B35-1: REDCMethod.sqdmulhMontgomery (CRÍTICO, 2-3 días)

**Objetivo**: Implementar sqdmulh REDC como alternativa al vmull REDC en SIMDEmitter.

**Tareas**:
1. Agregar `REDCMethod` a `BoundPropagation.lean` junto a `ReductionChoice`:
   ```lean
   inductive REDCMethod where
     | vmullWidening     -- actual: 2-lane vmull_u32, ~20 instrucciones
     | sqdmulhMontgomery -- nuevo: 4-lane vqdmulhq_s32, ~7+3 instrucciones
     deriving Repr, BEq, Inhabited
   ```

2. Agregar `redcMethod : REDCMethod := .vmullWidening` a `NTTStage` en NTTPlan.lean:65-73

3. Agregar `redcInstructionCost` a `CrossRelNTT.lean` (junto a `butterflyREDCCost`):
   ```lean
   def redcCost (method : REDCMethod) (hw : HardwareCost) : Nat :=
     match method with
     | .vmullWidening => butterflyREDCCost hw  -- actual
     | .sqdmulhMontgomery =>
       if hw.isSimd then hw.mul32 + hw.mul32 + hw.sub + 3  -- 7 instrucciones
       else butterflyREDCCost hw  -- scalar: vmull es mejor (no hay vqdmulhq)
   ```

4. Actualizar `butterflyCost` en NTTPlan.lean para usar `stage.redcMethod`:
   ```lean
   def butterflyCost (stage : NTTStage) (hw : HardwareCost) : Nat :=
     let redc := redcCost stage.redcMethod hw
     match stage.radix with
     | .r2 => hw.mul32 + 2 * hw.add + redc
     | .r4 => 3 * hw.mul32 + 8 * hw.add + 4 * redc
   ```

5. Crear `emitNeonButterflyBody_sqdmulh` en SIMDEmitter.lean — adaptar de
   UnifiedCodeGen.lean:439-465 (referencia huérfana). NO copiar — extraer la lógica
   compartida y crear un dispatch por REDCMethod.

6. Precomputar tabla `mu_tw[]` en OptimizedNTTPipeline.lean:
   ```lean
   let muTw := twiddles.map fun tw => (tw * mu) % (2^32)
   ```
   El C generado incluye `const int32_t mu_tw[] = { ... };`

7. Actualizar `generateCandidates` en NTTPlanSelection.lean para generar candidatos
   con `.sqdmulhMontgomery` cuando `hw.isSimd`:
   ```lean
   -- Nuevo candidato: R2 Harvey + sqdmulh REDC
   mkUniformPlan p n .r2 .harvey (redcMethod := .sqdmulhMontgomery),
   ```

8. Validar: NEON sqdmulh output vs Python reference para BabyBear/KoalaBear N=2^14

**Archivos a leer**: `UnifiedCodeGen.lean:439-465`, `SIMDEmitter.lean:56-95`, `NTTPlan.lean:65-73, 208-222`
**Archivos a modificar**: `BoundPropagation.lean`, `NTTPlan.lean`, `CrossRelNTT.lean`, `SIMDEmitter.lean`, `NTTPlanSelection.lean`, `OptimizedNTTPipeline.lean`
**Gate**: lake build + validation PASS + benchmark muestra mejora NEON

### B35-2: Calibración REDCMethod (PARALELO, 2 días)

**Objetivo**: Medir el costo real de sqdmulh vs vmull, validar que el cost model
predice correctamente el orden relativo, y calibrar `redcCost` con datos empíricos.

**Por qué es crítico**: El cost model determina QUÉ plan gana la competición en
`selectPlan`. Si `redcCost(.sqdmulhMontgomery)` está mal calibrado, el framework
podría elegir vmull cuando sqdmulh es mejor (o viceversa). Esto ya pasó con
`wideningPenalty=8` que inflaba Solinas NEON a 14 ciclos cuando el real era ~6.
Con más dimensiones, el riesgo de inversión de orden se multiplica.

**Principio**: El cost model no necesita predecir ciclos absolutos. Necesita
predecir **orden relativo** (¿es A más barato que B?). Calibramos para que el
ratio predicho vs real esté dentro de ±20%.

---

#### Paso 1: Microbenchmarks aislados de REDC (Fuente primaria)

Crear `Tests/benchmark/bench_redc_isolated.c` con dos funciones aisladas que
miden EXCLUSIVAMENTE el REDC, sin butterfly ni loop overhead:

```c
#include <arm_neon.h>
#include <time.h>
#include <stdio.h>

// REDC vmull widening (actual — copiar de SIMDEmitter output)
static inline int32x4_t redc_vmull(int32x4_t b, int32x4_t tw,
    uint32x4_t p_vec, uint32x4_t mu_vec) {
    // ... pegar las ~20 instrucciones de emitNeonButterflyBody ...
    // Retornar wb_red
}

// REDC sqdmulh Montgomery (nuevo — copiar de B35-1 output)
static inline int32x4_t redc_sqdmulh(int32x4_t b, int32x4_t tw,
    int32x4_t mu_tw, int32x4_t p_vec_s) {
    // ... pegar las ~7 instrucciones de emitNeonButterflyBody_sqdmulh ...
    // Retornar wb_red (canonicalizado a [0,p))
}

int main() {
    const int N = 10000000;  // 10M iteraciones
    int32_t data[4] = {100, 200, 300, 400};
    int32_t tw[4]   = {500, 600, 700, 800};
    // ... setup p_vec, mu_vec, mu_tw ...

    struct timespec t0, t1;

    // Benchmark vmull
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < N; i++) {
        int32x4_t b = vld1q_s32(data);
        int32x4_t w = vld1q_s32(tw);
        int32x4_t result = redc_vmull(b, w, p_vec, mu_vec);
        vst1q_s32(data, result);  // prevent dead code elimination
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double vmull_ns = (t1.tv_sec - t0.tv_sec) * 1e9 + (t1.tv_nsec - t0.tv_nsec);
    printf("vmull:  %.2f ns/call (%.2f ns/element)\n", vmull_ns/N, vmull_ns/(N*4));

    // Benchmark sqdmulh (mismos datos, reset)
    data[0]=100; data[1]=200; data[2]=300; data[3]=400;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < N; i++) {
        int32x4_t b = vld1q_s32(data);
        int32x4_t w = vld1q_s32(tw);
        int32x4_t result = redc_sqdmulh(b, w, mu_tw_vec, p_vec_s);
        vst1q_s32(data, result);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double sqdmulh_ns = (t1.tv_sec - t0.tv_sec) * 1e9 + (t1.tv_nsec - t0.tv_nsec);
    printf("sqdmulh: %.2f ns/call (%.2f ns/element)\n", sqdmulh_ns/N, sqdmulh_ns/(N*4));

    printf("Ratio vmull/sqdmulh: %.2fx\n", vmull_ns / sqdmulh_ns);
    return 0;
}
```

Compilar con: `clang -O2 -target aarch64-linux-gnu -mcpu=cortex-a76 bench_redc_isolated.c -o bench_redc`

**Resultado esperado**: ratio vmull/sqdmulh entre 1.5× y 2.5×.
**Si < 1.2×**: el compilador está optimizando agresivamente vmull o tiene overhead
en sqdmulh. Revisar el assembly (`clang -S -O2`) para ver qué instrucciones genera.

---

#### Paso 2: Verificar assembly generado con `llvm-mca`

Extraer el assembly de ambos REDC y simular scheduling:

```bash
# Generar assembly
clang -O2 -target aarch64-linux-gnu -mcpu=cortex-a76 -S bench_redc_isolated.c -o bench_redc.s

# Extraer solo el REDC vmull (buscar label redc_vmull)
# Simular throughput y bottleneck
llvm-mca -mcpu=cortex-a76 --timeline redc_vmull.s

# Repetir para sqdmulh
llvm-mca -mcpu=cortex-a76 --timeline redc_sqdmulh.s
```

`llvm-mca` reporta:
- **Iterations**: ciclos por iteración
- **IPC**: instrucciones por ciclo
- **Bottleneck**: qué recurso limita (V0 port, V1 port, register file, etc.)
- **Timeline**: diagrama de Gantt mostrando qué instrucción se ejecuta en qué ciclo

Registrar estos números — son la verdad del scheduling.

**Si llvm-mca no está disponible**: usar `perf stat` en el microbenchmark:
```bash
perf stat -e cycles,instructions,r0073 ./bench_redc  # r0073 = NEON instructions
```

---

#### Paso 3: Construir InstructionProfile para cada REDC

Modelo de costo detallado que reemplaza el número único actual. Crear o actualizar
en `CrossRelNTT.lean` (junto a `reductionCostForHW`):

```lean
/-- Instruction profile for modelling execution cost.
    Critical path = longest dependency chain (bounds latency).
    V0-only = multiply-unit instructions (bounds throughput on V0 pipe).
    V0/V1 = dual-issuable instructions (can run on either pipe). -/
structure InstructionProfile where
  criticalPathCycles : Nat  -- cycles of longest dependency chain
  v0OnlyInstructions : Nat  -- instructions exclusive to V0 (mul, sqdmulh)
  dualIssueInstructions : Nat -- instructions for V0 or V1 (add, sub, cmp, and)
  deriving Repr

/-- Effective cost: max of critical path, V0 saturation, total throughput.
    This models a 2-pipe out-of-order ARM NEON core (V0 + V1). -/
def effectiveCost (profile : InstructionProfile) : Nat :=
  let v0Throughput := profile.v0OnlyInstructions  -- 1 per cycle on V0
  let totalInstr := profile.v0OnlyInstructions + profile.dualIssueInstructions
  let totalThroughput := (totalInstr + 1) / 2  -- 2 pipes, round up
  Nat.max profile.criticalPathCycles (Nat.max v0Throughput totalThroughput)
```

Valores iniciales (de ARM Cortex-A76 Software Optimization Guide):

```lean
/-- vmull widening REDC profile.
    Chain: vmull(4) → vmovn(2) → vmul(4) → vmull(4) → vsub(2) → vshrn(2) = 18 cyc
    V0-only: vmull×4 + vmul×2 = 6 instructions
    Dual: vmovn×2 + vsub×2 + vshrn×2 + vclt×2 + vmovn×2 + vand+vadd = ~12 -/
def redcProfile_vmull : InstructionProfile :=
  { criticalPathCycles := 18, v0OnlyInstructions := 6, dualIssueInstructions := 12 }

/-- sqdmulh Montgomery REDC profile (incl. canonicalization).
    Chain: sqdmulh(4) ∥ mul(4) → sqdmulh(4) → shsub(2) → clt(2) → and(2) → add(2) = 16 cyc
    (First sqdmulh and mul are INDEPENDENT, execute in parallel → 4 not 8)
    V0-only: sqdmulh×2 + mul×1 = 3 instructions
    Dual: shsub + clt + and + add = 4 instructions -/
def redcProfile_sqdmulh : InstructionProfile :=
  { criticalPathCycles := 16, v0OnlyInstructions := 3, dualIssueInstructions := 4 }
```

**IMPORTANTE**: Estos valores son iniciales basados en la documentación. El Paso 4
los corrige con datos empíricos.

Referencia: ARM Cortex-A76 Software Optimization Guide (DAI 0553), Table 3-1:
- `SQDMULH Qd,Qn,Qm`: Result latency 4, Execution throughput 1
- `MUL Qd,Qn,Qm (32-bit)`: Result latency 4, Execution throughput 1
- `UMULL Qd,Dn,Dm`: Result latency 4 (note: Dd not Qd — 2 lanes)
- `SHSUB Qd,Qn,Qm`: Result latency 2, Execution throughput 2
- `ADD Qd,Qn,Qm`: Result latency 2, Execution throughput 2
- `CMGE Qd,Qn,Qm`: Result latency 2, Execution throughput 2

---

#### Paso 4: Calibrar con datos empíricos

Comparar:
- `effectiveCost(redcProfile_vmull)` vs tiempo medido en Paso 1
- `effectiveCost(redcProfile_sqdmulh)` vs tiempo medido en Paso 1

**Caso A: El ratio predicho coincide con el medido (±20%)**
→ El modelo funciona. Usar `effectiveCost` directamente en `redcCost`.

**Caso B: El ratio predicho está invertido (modelo dice A < B, realidad dice A > B)**
→ ERROR CRÍTICO. Revisar:
  1. ¿El compilador reorganizó el código? Verificar con `clang -S -O2`.
  2. ¿Hay stalls de register spilling? Verificar con `perf stat -e r0170` (stall cycles).
  3. ¿El critical path tiene dependencias que el modelo no captura?
  Ajustar `criticalPathCycles` hasta que el orden se corrija.

**Caso C: El ratio predicho tiene la dirección correcta pero magnitud incorrecta (>20%)**
→ Agregar factor de corrección empírico a HardwareCost:
```lean
structure HardwareCost where
  ...
  -- Empirical correction for sqdmulh REDC efficiency
  -- 100 = theoretical throughput. <100 = real is worse. >100 = real is better.
  sqdmulhEfficiency : Nat := 100
```
Y en `redcCost`:
```lean
| .sqdmulhMontgomery =>
    effectiveCost redcProfile_sqdmulh * 100 / hw.sqdmulhEfficiency
```

---

#### Paso 5: Benchmark NTT completo

Después de calibrar el REDC aislado, correr el NTT completo para verificar que
el gain del REDC se traslada al NTT:

```
# Con vmull (baseline — forzar REDCMethod.vmullWidening en el plan)
Tests/benchmark/benchmark.py --pipeline ultra --hardware arm-neon --redc vmull

# Con sqdmulh (nuevo — plan selecciona sqdmulhMontgomery automáticamente)
Tests/benchmark/benchmark.py --pipeline ultra --hardware arm-neon --redc sqdmulh

# Comparar con P3 real (de B35-0)
Tests/benchmark/benchmark.py --pipeline p3-real --hardware arm-neon
```

**Resultado esperado**: gain sqdmulh/vmull en NTT completo ≈ 60-80% del gain
aislado (el resto del NTT — loads, stores, Harvey reduce — no cambia).

Si el gain en NTT < 40% del gain aislado → memory bandwidth domina, no ALU.
Esto indicaría que las optimizaciones siguientes (ILP, blocking) son más
importantes de lo previsto.

---

#### Paso 6: Registrar y documentar

En BENCHMARKS.md, agregar sección con:

```markdown
## B35-2: REDC Calibration Results (fecha)

### Microbenchmark aislado (N=10M, Cortex-A76/Apple M-series)
| REDC Method | ns/call | ns/element | Instructions (llvm-mca) |
|---|---|---|---|
| vmull widening | X.XX | X.XX | XX |
| sqdmulh Montgomery | X.XX | X.XX | XX |
| **Ratio** | **X.Xx** | | |

### Model vs Reality
| Metric | Model prediction | Measured | Error |
|---|---|---|---|
| effectiveCost(vmull) | XX | XX | XX% |
| effectiveCost(sqdmulh) | XX | XX | XX% |
| Ratio vmull/sqdmulh | X.Xx | X.Xx | XX% |

### Calibration applied
- sqdmulhEfficiency: 100 → XX (if adjusted)
- criticalPathCycles: XX → XX (if adjusted)

### NTT completo (BabyBear N=2^16, NEON)
| Config | μs | vs vmull | vs P3-real |
|---|---|---|---|
| Ultra (vmull REDC) | XXX | baseline | +XX% |
| Ultra (sqdmulh REDC) | XXX | +XX% | +XX% |
| P3 real (monty-31) | XXX | — | baseline |
```

**Archivos a crear**: `Tests/benchmark/bench_redc_isolated.c`
**Archivos a modificar**: `CrossRelNTT.lean` (InstructionProfile, effectiveCost),
  `CostModelDef.lean` (sqdmulhEfficiency en HardwareCost si necesario), `BENCHMARKS.md`
**Archivos a leer**: Output de B35-1 (SIMDEmitter.lean con sqdmulh body),
  ARM Cortex-A76 Software Optimization Guide (DAI 0553) Table 3-1,
  assembly generado por clang -S -O2

**Gate**:
1. Microbenchmark compila y corre, produce números reproducibles (±5% entre runs)
2. `effectiveCost` predice el ratio vmull/sqdmulh con error < 20%
3. Si no: constantes ajustadas y documentadas en BENCHMARKS.md
4. NTT completo sqdmulh ≥ NTT vmull (sin regresión)

### B35-3: ILPFactor (CRÍTICO, 2 días)

**Objetivo**: Agregar `ilpFactor` a NTTStage, modificar emitter para dual-butterfly.

**Prerequisito**: B35-1 (sqdmulh reduce register pressure, habilitando ilpFactor=2)

**Tareas**:
1. Agregar `ilpFactor : Nat := 1` a `NTTStage` en NTTPlan.lean

2. Actualizar `Plan.totalCost` en NTTPlan.lean para descontar latency hiding:
   ```lean
   let ilpDiscount := if stage.ilpFactor > 1 && hw.isSimd
     then Nat.max 1 (rawStageCost * 3 / 4)  -- ~25% discount for dual-issue
     else rawStageCost
   ```

3. Modificar `emitStageC` en SIMDEmitter.lean:
   ```lean
   let step := if stage.ilpFactor > 1 then 2 * lanes else lanes
   -- Inner loop:
   for (pr = 0; pr < halfSize; pr += step) {
       bf(&data[i], &data[j], &tw[tw_idx], ...);
       if (step > lanes)
           bf(&data[i+lanes], &data[j+lanes], &tw[tw_idx+lanes], ...);
   }
   ```

4. Agregar candidato con ilpFactor=2 a `generateCandidates`

5. Validar: output numérico idéntico (ilpFactor no cambia la matemática)

**Archivos a leer**: `SIMDEmitter.lean:241-269`, `NTTPlan.lean:216-235`
**Archivos a modificar**: `NTTPlan.lean`, `SIMDEmitter.lean`, `NTTPlanSelection.lean`
**Gate**: lake build + validation PASS + benchmark muestra mejora adicional

### B35-4: Calibración ILP (PARALELO, 2 días)

**Objetivo**: Medir el gain real de ilpFactor=2, verificar si el compilador ya hace
interleaving automático, y calibrar el descuento ILP en el cost model.

**Por qué no es "similar a B35-2"**: ILP tiene una complicación que REDC no tiene:
el compilador C con `-O2` ya hace instruction scheduling. Si clang reordena las
instrucciones de un solo butterfly para llenar pipes idle, ilpFactor=2 podría dar
MENOS gain del esperado (porque el compiler ya captura parte del beneficio). Si
clang NO reordena (porque el butterfly tiene una cadena de dependencias tight),
ilpFactor=2 da el gain completo. Hay que verificar empíricamente.

---

#### Paso 1: Verificar auto-interleaving del compilador

ANTES de medir, examinar qué hace el compilador con ilpFactor=1:

```bash
# Compilar el NTT con ilpFactor=1 (actual) y generar assembly
clang -O2 -target aarch64-linux-gnu -mcpu=cortex-a76 -S ntt_ultra.c -o ntt_ilp1.s

# Buscar si el compilador intercala instrucciones de iteraciones distintas
# del inner loop. Señal: instrucciones de load de iteración N+1 antes de
# que termine el store de iteración N.
grep -A5 -B5 "vst1q" ntt_ilp1.s | head -40
```

**Si el assembly muestra interleaving natural** (loads de la siguiente iteración
antes de stores de la actual):
→ El compilador ya hace software pipelining. ilpFactor=2 dará gain marginal (~5-10%).
→ Documentar: "compiler auto-interleaves, ilpFactor=2 redundante para este target".
→ El cost model debería NO aplicar descuento ILP (o aplicar uno mínimo).

**Si el assembly es estrictamente secuencial** (todas las instrucciones de butterfly N
completan antes de empezar butterfly N+1):
→ El compilador no puede interleave por dependencias. ilpFactor=2 ayuda mucho.
→ Gain esperado: 20-40%.

---

#### Paso 2: Microbenchmark aislado — ilpFactor=1 vs ilpFactor=2

Crear `Tests/benchmark/bench_ilp_isolated.c`:

```c
#include <arm_neon.h>
#include <time.h>
#include <stdio.h>

// Butterfly + Harvey (copiar de output B35-1, sqdmulh version)
static inline void neon_bf_dit_har(int32_t* a_ptr, int32_t* b_ptr,
    const int32_t* tw_ptr, /* ... params ... */) {
    // ... butterfly completa ...
}

// Inner loop con ilpFactor=1
void ntt_stage_ilp1(int32_t* data, const int32_t* twiddles,
    int halfSize, int numGroups, int lanes, /* ... */) {
    for (int grp = 0; grp < numGroups; grp++) {
        for (int pr = 0; pr < halfSize; pr += lanes) {
            int i = grp * 2 * halfSize + pr;
            int j = i + halfSize;
            neon_bf_dit_har(&data[i], &data[j], &twiddles[tw_idx], /* ... */);
        }
    }
}

// Inner loop con ilpFactor=2
void ntt_stage_ilp2(int32_t* data, const int32_t* twiddles,
    int halfSize, int numGroups, int lanes, /* ... */) {
    for (int grp = 0; grp < numGroups; grp++) {
        for (int pr = 0; pr < halfSize; pr += 2 * lanes) {
            int i = grp * 2 * halfSize + pr;
            int j = i + halfSize;
            // Dos butterflies consecutivas — le da al compiler más trabajo
            // independiente para scheduling
            neon_bf_dit_har(&data[i],       &data[j],       &twiddles[tw_idx],       /* ... */);
            neon_bf_dit_har(&data[i+lanes], &data[j+lanes], &twiddles[tw_idx+lanes], /* ... */);
        }
    }
}

int main() {
    // Setup: N=65536, BabyBear, stage 0 (halfSize=32768)
    const int N = 65536;
    int32_t* data = aligned_alloc(64, N * sizeof(int32_t));
    int32_t* tw   = aligned_alloc(64, (N/2) * sizeof(int32_t));
    // ... init data y twiddles ...

    const int REPS = 1000;
    struct timespec t0, t1;

    // Benchmark ilp1
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int r = 0; r < REPS; r++)
        ntt_stage_ilp1(data, tw, N/2, 1, 4, /* ... */);
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double ilp1_us = ((t1.tv_sec-t0.tv_sec)*1e6 + (t1.tv_nsec-t0.tv_nsec)/1e3) / REPS;

    // Benchmark ilp2
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int r = 0; r < REPS; r++)
        ntt_stage_ilp2(data, tw, N/2, 1, 4, /* ... */);
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double ilp2_us = ((t1.tv_sec-t0.tv_sec)*1e6 + (t1.tv_nsec-t0.tv_nsec)/1e3) / REPS;

    printf("ilp1: %.2f μs/stage\n", ilp1_us);
    printf("ilp2: %.2f μs/stage\n", ilp2_us);
    printf("Gain: %.1f%%\n", (1.0 - ilp2_us/ilp1_us) * 100);

    free(data); free(tw);
    return 0;
}
```

Compilar con: `clang -O2 -target aarch64-linux-gnu -mcpu=cortex-a76 bench_ilp_isolated.c -o bench_ilp`

**Resultado esperado**: gain entre 10% y 40% dependiendo de auto-interleaving del compiler.

---

#### Paso 3: Medir V0/V1 pipe occupancy (opcional, si `perf` disponible)

Si el hardware tiene PMU (Performance Monitoring Unit) accesible:

```bash
# Cortex-A76 PMU events:
# 0x0073 = ASE_SPEC (NEON speculative instructions)
# 0x0170 = STALL_BACKEND (pipeline stalls)
# 0x0008 = INST_RETIRED (retired instructions)
perf stat -e cycles,instructions,r0073,r0170 ./bench_ilp
```

Comparar STALL_BACKEND entre ilp1 e ilp2:
- Si ilp2 tiene significativamente menos stalls → ILP está escondiendo latencia
- Si stalls similares → el bottleneck es otro (memory, register spill)

---

#### Paso 4: Construir modelo ILP

Modelo que reemplaza el `ilpDiscount = rawCost * 3/4` simplista de B35-3.

Necesitamos el InstructionProfile del butterfly COMPLETO (no solo REDC):

```lean
/-- Full butterfly profile: REDC + DIT sum/diff + Harvey reduce.
    Built from redcProfile + reduction profile. -/
def butterflyProfile (redcMethod : REDCMethod) : InstructionProfile :=
  let redc := match redcMethod with
    | .vmullWidening => redcProfile_vmull
    | .sqdmulhMontgomery => redcProfile_sqdmulh
  -- DIT sum/diff: add(a,wb) + add(a,p) + sub = 3 dual-issue
  -- Harvey reduce sum: cge + and + sub = 3 dual-issue
  -- Harvey reduce diff: cge + and + sub = 3 dual-issue
  -- Total dual-issue added: 9
  { criticalPathCycles := redc.criticalPathCycles + 6  -- sum/diff/harvey chain
    v0OnlyInstructions := redc.v0OnlyInstructions
    dualIssueInstructions := redc.dualIssueInstructions + 9 }
```

Modelo de gain ILP:

```lean
/-- ILP gain: how many cycles V1 can absorb from a second butterfly
    while V0 is busy with the first butterfly's multiply chain.
    Returns: effective cost reduction per butterfly pair. -/
def ilpGain (profile : InstructionProfile) (ilpFactor : Nat) : Nat :=
  if ilpFactor ≤ 1 then 0
  else
    -- V1 idle time = V0-only instructions of first butterfly
    -- (V1 has nothing to do while V0 executes multiplies)
    let v1IdleTime := profile.v0OnlyInstructions
    -- V1 can absorb this many dual-issue instructions from the second butterfly
    let v1Absorbable := min v1IdleTime profile.dualIssueInstructions
    -- Each absorbed instruction saves ~2 cycles (one dual-issue slot)
    v1Absorbable

/-- Cost model with ILP discount. -/
def stageCostWithILP (rawCost : Nat) (profile : InstructionProfile)
    (ilpFactor : Nat) (hw : HardwareCost) : Nat :=
  if !hw.isSimd || ilpFactor ≤ 1 then rawCost
  else
    let gainPerPair := ilpGain profile ilpFactor
    -- Gain is per pair of butterflies. Amortize over the pair.
    -- Conservative: don't assume more than 30% reduction (compiler already helps)
    let maxDiscount := rawCost * 30 / 100
    rawCost - min gainPerPair maxDiscount
```

**IMPORTANTE**: El `maxDiscount` de 30% es un tope conservador. Se ajusta en el
Paso 5 con datos empíricos.

---

#### Paso 5: Calibrar con datos empíricos

Comparar predicción del modelo vs medición:

```
Modelo: ilpGain(sqdmulhButterflyProfile, 2) = X ciclos
        → discount = min(X, 30% de rawCost) = Y%
Medido: gain ilp2 vs ilp1 = Z%
```

**Caso A: Y ≈ Z (±10 puntos porcentuales)**
→ Modelo funciona. Usar `stageCostWithILP` en `Plan.totalCost`.

**Caso B: Y > Z (modelo sobreestima ILP gain)**
→ Posibles causas:
  1. Compiler ya hace auto-interleaving (Paso 1 debió detectarlo)
  2. Register spilling: 2 butterflies en vuelo exceden 32 registros NEON,
     causando loads/stores extras que anulan el gain de ILP.
     Verificar: `perf stat -e r0170` (stall backend) y contar spills en assembly.
  3. Memory bandwidth: 2 butterflies cargan el doble de datos simultáneamente,
     saturando el bus L1→register.
→ Reducir `maxDiscount` hasta que Y ≈ Z.

**Caso C: Y < Z (modelo subestima ILP gain)**
→ El gain real es mayor de lo esperado. Subir `maxDiscount` o eliminar el tope.
→ Posible causa: el compiler usa ilpFactor=2 para hacer loop unrolling + scheduling
  que beneficia más allá de V0/V1 parallelism (mejor branch prediction, prefetch).

---

#### Paso 6: Benchmark NTT completo con ILP

```
# Sin ILP (forzar ilpFactor=1)
Tests/benchmark/benchmark.py --pipeline ultra --hardware arm-neon --ilp 1

# Con ILP (ilpFactor=2, plan lo selecciona si el cost model lo prefiere)
Tests/benchmark/benchmark.py --pipeline ultra --hardware arm-neon --ilp 2

# Comparar
```

**Si el gain en NTT completo < 50% del gain aislado** (Paso 2):
→ El bottleneck en NTT completo no es ALU sino memoria.
→ Esto es información valiosa para B35-5 (stage merging decision).
→ Documentar: "ALU optimizations (REDC + ILP) gave X%, remaining bottleneck is memory.
   Stage merging (memory optimization) becomes high priority."

**Si el gain en NTT completo ≈ gain aislado**:
→ ALU es el bottleneck dominante. Stage merging tiene menos prioridad.

---

#### Paso 7: Verificar efecto en scalar (regresión check)

```
# Scalar con ilpFactor=1 (actual)
Tests/benchmark/benchmark.py --pipeline ultra --hardware arm-scalar --ilp 1

# Scalar con ilpFactor=2
Tests/benchmark/benchmark.py --pipeline ultra --hardware arm-scalar --ilp 2
```

En scalar, ilpFactor=2 debería ser neutral o ligeramente negativo (overhead de
loop con step=2*1=2 vs step=1, sin pipes SIMD para explotar).

El cost model debería NO seleccionar ilpFactor=2 para scalar porque
`!hw.isSimd → discount = 0`. Verificar que el plan generado para scalar
efectivamente tiene ilpFactor=1.

---

#### Paso 8: Registrar y documentar

En BENCHMARKS.md:

```markdown
## B35-4: ILP Calibration Results (fecha)

### Compiler auto-interleaving check
- Compiler: clang X.Y, -O2 -mcpu=cortex-a76
- Auto-interleaving detected: YES/NO
- Evidence: [paste relevant assembly snippet]

### Microbenchmark aislado (stage 0, N=65536, Cortex-A76)
| ilpFactor | μs/stage | Gain vs ilp=1 |
|---|---|---|
| 1 | X.XX | baseline |
| 2 | X.XX | +XX% |

### V0/V1 occupancy (if perf available)
| ilpFactor | Cycles | Instructions | IPC | Stall Backend |
|---|---|---|---|---|
| 1 | X | X | X.XX | X |
| 2 | X | X | X.XX | X |

### Model vs Reality
| Metric | Model prediction | Measured | Error |
|---|---|---|---|
| ilpGain(sqdmulhProfile, 2) | X cycles | — | — |
| Predicted discount | XX% | XX% (actual) | XX pp |

### Calibration applied
- maxDiscount: 30% → XX% (if adjusted)

### NTT completo (BabyBear N=2^16, NEON)
| Config | μs | vs baseline |
|---|---|---|
| sqdmulh + ilp=1 | XXX | baseline |
| sqdmulh + ilp=2 | XXX | +XX% |

### Scalar regression check
| Config | μs | vs baseline |
|---|---|---|
| vmull + ilp=1 (scalar) | XXX | baseline |
| vmull + ilp=2 (scalar) | XXX | +XX% (expect ~0%) |

### Conclusion for B35-5 (stage merging decision)
- ALU-bound or memory-bound? [based on isolated vs NTT gain ratio]
- Late stages (10-15) percentage of total: XX% [from profiling]
- Stage merging recommendation: [PROCEED / DEFER]
```

**Archivos a crear**: `Tests/benchmark/bench_ilp_isolated.c`
**Archivos a modificar**: `CrossRelNTT.lean` (butterflyProfile, ilpGain, stageCostWithILP),
  `NTTPlan.lean` (Plan.totalCost con ILP model), `BENCHMARKS.md`
**Archivos a leer**: Assembly de B35-3 (`clang -S -O2`), ARM Cortex-A76 Software
  Optimization Guide Table 3-1, output de `llvm-mca` o `perf stat`

**Gate**:
1. Microbenchmark compila y corre, gain ≥ 5% (si < 5%, ILP no justifica complejidad)
2. Cost model predice gain con error < 15 puntos porcentuales
3. Scalar sin regresión (< 3% variación)
4. NTT completo con ILP ≥ NTT sin ILP
5. BENCHMARKS.md tiene tabla completa con números reales

### B35-5: Decisión Stage Merging / Memory Optimization (HOJA, 2-3 días)

**Objetivo**: Con los datos de B35-4 (bottleneck = memoria, no ALU), evaluar tres
estrategias de optimización de memoria y decidir cuál implementar en v3.6.0.

**Por qué este bloque cambió de alcance**: B35-4 demostró que clang -O2 ya maximiza
el scheduling ALU. El bottleneck es memory bandwidth y cache misses. Esto redefine
la pregunta de "¿mergear late stages?" a "¿cuál es la mejor forma de reducir tráfico
de memoria?". Hay tres opciones con perfiles muy diferentes.

---

#### Contexto: Distribución real del tiempo por stages (N=65536, NEON)

Para BabyBear N=2^16, los 16 stages del NTT tienen exactamente el mismo número
de butterflies (8192 cada uno). La diferencia está en el **costo de cache**:

| Grupo | Stages | halfSize | Stride (bytes) | Cache behavior | % del tiempo |
|-------|--------|----------|----------------|----------------|-------------|
| **Early** | 0-2 | 32768-8192 | 128K-32K | **L1 miss en CADA butterfly** (~10 cyc extra) | ~26% |
| **Mid-early** | 3-4 | 4096-2048 | 16K-8K | L1 miss parcial (~5 cyc extra) | ~12% |
| **Mid-late** | 5-9 | 1024-64 | 4K-256B | L1 hit | ~31% |
| **Late** | 10-15 | 32-1 | 128B-4B | L1 hit, stages 13-15 scalar | ~31% |

**Observación clave**: los early stages (0-4) pagan ~35-38% del tiempo total
a pesar de tener solo 5/16 = 31% de los butterflies, porque cada butterfly
tiene ~10 ciclos extra de cache miss penalty. Esto NO se resuelve con stage
merging de late stages.

---

#### Opción A: Late-Stage Merging (stages 12-15, "bottom" merge)

**Qué es**: Cargar bloques de 16 elementos en 4 NEON registers, procesar stages
12-15 in-register con transposes `trn1/trn2` entre stages, store una vez.

**Evidencia de producción**: neon-ntt (Dilithium TCHES 2022) usa exactamente este
patrón como `_bot` function. Para N=256 con 32-bit elements, fusiona 4 stages
con bloques de 16 elementos.

**Mecánica de transposes**: 8 instrucciones `trn1/trn2` por transpose (2 fases:
32-bit interleave + 64-bit interleave). Se necesita 1 transpose entre cada par
de stages fusionados = 3 transposes × 8 instrucciones = 24 instrucciones extra
amortizadas en 16 butterflies del bloque = ~1.5 instrucciones/butterfly.

**Register budget** (de neon-ntt source code):
```
Data set 1:    v0-v3   (4 regs, 16 elementos)
Data set 2:    v4-v7   (4 regs, para interleaving con set 1)
Temporales:    v8-v15  (8 regs, para transpose y REDC intermedios)
Twiddles:      v16-v23 (8 regs, preloaded per-block)
Constants:     v24-v27 (4 regs: p, mu, etc.)
Spare:         v28-v31 (4 regs)
Total: 32/32 NEON registers usados.
```

**Gain estimado**: Stages 12-15 = ~4/16 = ~25% del NTT. Merging elimina 3
store+load roundtrips entre stages = ~3 × 8192 × 8 bytes × 2 (load+store)
= ~394K memory ops eliminadas. A ~4 ciclos/op L1 = ~1.6M ciclos ahorrados.
Sobre ~20M ciclos totales (estimado para N=65536) = **~8% mejora**.

**Complejidad**: Media. Nuevo emitter `emitMergedStagesC` + transpose helpers.
~300-400 LOC nuevas en SIMDEmitter.lean.

**Riesgo**: Bajo. La técnica está probada en producción (Dilithium).

---

#### Opción B: Cache Blocking para Early Stages (stages 0-4)

**Qué es**: En vez de procesar stage 0 completo, luego stage 1 completo, etc.,
procesar BLOQUES del array a través de múltiples stages. Un bloque de B elementos
pasa por stages 0-4 antes de pasar al siguiente bloque. Esto mantiene el working
set en L1/L2 cache.

**Ejemplo concreto** para N=65536, blockSize=8192 (32KB, cabe en L1):
```
Actual (por stage):
  Stage 0: procesar ALL 65536 elementos (256KB, blows L1)
  Stage 1: procesar ALL 65536 elementos (256KB, blows L1)
  ...
  
Blocked:
  Block 0 (data[0..8191]):
    Stage 0 butterflies que tocan [0..8191]  → sub-block cabe en L1
    Stage 1 butterflies que tocan [0..8191]  → mismo data, aún en L1
    ... hasta stage 4 ...
  Block 1 (data[8192..16383]):
    Stage 0 butterflies que tocan [8192..16383]
    ...
```

**El problema**: las butterflies de stage 0 usan stride=32768. Un butterfly
en posición 0 toca data[0] y data[32768]. Para que ambos estén en el bloque,
el bloque debería ser de tamaño ≥65536 = todo el array. **Blocking no ayuda
para stages con stride > blockSize.**

**Solución real**: Solo los stages con stride ≤ blockSize/2 pueden bloquearse.
Para blockSize=8192: stages 4+ (stride ≤ 4096). Stages 0-3 siguen sin blocking.
El gain se limita a stages 3-4 que están en la zona L1-miss parcial.

**La infraestructura ya existe**: `VerifiedNTTOptimizations.lean:220-356` tiene
`lowerNTTLoopBlocked` con `blockableFrom` que identifica exactamente desde qué
stage se puede bloquear. Theorem `butterfly_groups_disjoint` prueba que los
bloques no se solapan.

**Gain estimado**: Stages 3-4 = ~12% del tiempo. Blocking reduce su cache miss
penalty de ~5 ciclos a ~1 ciclo. Gain = 12% × (4/5) = **~10% mejora**.

**Complejidad**: Baja-media. La infraestructura Lean ya existe. Falta conectar
`lowerNTTLoopBlocked` con SIMDEmitter o crear un emitter bloqueado.

**Riesgo**: Bajo. El code path verificado ya existe en Lean.

---

#### Opción C: Four-Step NTT (Bailey's Algorithm)

**Qué es**: Descomponer el NTT de tamaño N en NTTs más pequeños usando la
identidad algebraica. Para N = N1 × N2:

```
NTT_N(x) = Transpose · DiagTwiddle · (N1 copies of NTT_{N2}) · Transpose · (N2 copies of NTT_{N1})
```

Para N=65536 = 256 × 256:
1. Tratar data[65536] como matrix 256×256 (filas de 256 elementos = 1KB)
2. Hacer 256 NTTs de tamaño 256 por fila → CADA UNO cabe en L1 (1KB << 32KB)
3. Multiplicar por twiddle factors diagonales (streaming, O(N))
4. Transponer la matrix (O(N) con NEON ld4/st4)
5. Hacer 256 NTTs de tamaño 256 por fila de nuevo

**Por qué es transformativo**: TODOS los NTTs son de tamaño 256, que caben
en L1 y se pueden procesar con la técnica _top+_bot de neon-ntt (4 stages
individuales + 4 stages fusionados). El stride máximo dentro de cada sub-NTT
es 128 elementos = 512 bytes << L1. **Zero cache misses en el cómputo NTT.**

**Overhead**: La transposición es O(N) y el twiddle diagonal es O(N). Para
N=65536: ~131072 operaciones de overhead vs ~16 × 8192 = 131072 butterflies.
El overhead es ~1× las butterflies pero mucho más simple (load + store + mul).
Estimado: ~8-10% de overhead por los pasos extra.

**Gain estimado**: Elimina ~100% del cache miss penalty de early stages.
Early stages = ~35% del tiempo con ~10 ciclos extra por butterfly.
Gain = 35% × (10/22) ≈ **~16% mejora neta** (después de descontar overhead).
Para N=2^20 el gain sería mayor (~25%) porque el data set es 4MB vs L2 1MB.

**Compatibilidad con el framework**:
- Se modela como `NTTDecomposition` en el Plan:
  ```lean
  inductive NTTDecomposition where
    | standard            -- NTT directo, 16 stages
    | fourStep (n1 n2 : Nat)  -- Bailey: n1 × n2 sub-NTTs
  ```
- El cost model evalúa: `standard_cost` (con cache penalty) vs
  `fourStep_cost` (sin cache penalty, con overhead de transpose+twiddle).
- Para N pequeño (≤ 2^10, cabe en L1): `standard` gana (zero overhead).
- Para N grande (≥ 2^14, blows L1): `fourStep` gana.
- **El e-graph descubre cuándo four-step es mejor via cost model.**

**Complejidad**: Alta. Requiere:
1. Nuevo emitter para sub-NTTs de tamaño fijo (256 o 1024)
2. Emitter de transposición matricial con NEON (ld4/st4 para bloques 4×4)
3. Emitter de twiddle diagonal multiplication
4. Precomputación de twiddle tables para sub-NTTs + diagonal
5. Proof de equivalencia: `fourStepNTT(data) = standardNTT(data)`

**Riesgo**: Medio-alto. Cambio arquitectónico significativo en el emitter.

**Referencia**: Plonky3 usa una descomposición similar (`parallel DIT` con
split en `mid = ceil(log_h / 2)`). El paper de la CFNTT (TCHES 2023) analiza
four-step para FPGA pero el principio es idéntico para NEON.

---

#### Paso 1: Profiling empírico — confirmar distribución de tiempo

Antes de decidir, medir empíricamente qué stages dominan el tiempo:

```c
// En el C generado, agregar timestamps per-stage:
#include <time.h>

void ntt_ultra_profiled(int32_t* data, const int32_t* twiddles) {
    struct timespec t0, t1;
    // ... setup ...
    
    clock_gettime(CLOCK_MONOTONIC, &t0);
    // --- Stage 0 code ---
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double stage0_us = (t1.tv_sec-t0.tv_sec)*1e6 + (t1.tv_nsec-t0.tv_nsec)/1e3;
    
    clock_gettime(CLOCK_MONOTONIC, &t0);
    // --- Stage 1 code ---
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double stage1_us = ...;
    
    // ... repeat for all 16 stages ...
    
    printf("Stage distribution:\n");
    for (int s = 0; s < 16; s++)
        printf("  Stage %2d: %7.1f us (%5.1f%%)\n", s, stage_us[s], 
               100.0 * stage_us[s] / total_us);
}
```

Esto es un cambio temporal en OptimizedNTTPipeline.lean: agregar flag `--profiled`
que emite los `clock_gettime` entre stages.

**Si el profiling confirma** que early stages (0-4) > 30% del tiempo:
→ Opción C (four-step) o Opción A+B combinadas son necesarias.

**Si el profiling muestra** distribución uniforme (cada stage ~6.25%):
→ El cache miss penalty es menor de lo estimado (hardware prefetcher ayuda).
→ Opción A (late merge) es suficiente.

---

#### Paso 2: Evaluar las tres opciones

Con datos del profiling, completar esta tabla:

```markdown
| Criterio | A: Late Merge | B: Cache Block | C: Four-Step |
|----------|---------------|----------------|--------------|
| Gain estimado | ~8% | ~10% | ~16-25% |
| Aplica a early stages? | NO | PARCIAL (3-4) | SÍ (todos) |
| Aplica a late stages? | SÍ (12-15) | NO | SÍ (via sub-NTT) |
| Complejidad (LOC) | ~300-400 | ~150 (rewire) | ~800-1000 |
| Esfuerzo (días) | 5-7 | 3-4 | 10-15 |
| Riesgo | Bajo | Bajo | Medio-alto |
| Infraestructura existente | neon-ntt reference | VerifiedNTTOptimizations | Nada |
| Compatible con sqdmulh? | SÍ | SÍ | SÍ |
| Escalabilidad a N=2^20 | Misma (solo late) | Misma | MEJOR (gain crece) |
| Valor como dimensión del plan | BlockingConfig | BlockingConfig | NTTDecomposition |
```

---

#### Paso 3: Decisión y documentación

**Criterio de decisión**:

1. **Si early stages > 30% del tiempo Y N=2^20 es un target importante**:
   → **Opción C (four-step)** como v3.6.0. Es la única que ataca el bottleneck
   real (cache misses en early stages) y escala a N grandes.
   → Opción A como sub-componente (los sub-NTTs de 256 elementos usan late merge).

2. **Si early stages < 25% del tiempo (prefetcher helps)**:
   → **Opción A (late merge)** como v3.6.0. Simple, bajo riesgo, gain modesto.
   → Opción C diferida a v3.7.0 o posterior.

3. **Si la distribución es uniforme Y el gain total esperado < 10%**:
   → **Ninguna** en v3.6.0. El NTT ya es 2.6× Plonky3 reference y el
   esfuerzo de stage merging no justifica el gain marginal.
   → Pivotar a otras primitivas (FRI fold, polynomial commitment).

**Documentar** en ARCHITECTURE.md:
- Los datos de profiling por stage
- La tabla de evaluación de opciones
- La decisión tomada con justificación
- Si se elige C: DAG topológico para v3.6.0

---

**Archivos a crear**: `Tests/benchmark/ntt_profiled.c` (o flag `--profiled` en pipeline)
**Archivos a leer**: `VerifiedNTTOptimizations.lean:220-356` (cache blocking existente),
  `SIMDEmitter.lean:285-327` (loop structure actual), datos de B35-2 y B35-4
**Archivos a modificar**: `ARCHITECTURE.md` (decisión), `BENCHMARKS.md` (profiling data)

**Gate**:
1. Profiling per-stage completado para N=2^16 y N=2^20
2. Tabla de evaluación de opciones completada con datos reales
3. Decisión documentada en ARCHITECTURE.md con justificación
4. Si se elige A o C: DAG topológico para v3.6.0 con bloques detallados

---

## DAG Topológico

```
B35-0 [FUND] ──→ B35-1 [CRIT] ──→ B35-2 [PAR] ──→ B35-3 [CRIT] ──→ B35-4 [PAR] ──→ B35-5 [HOJA]
```

Estrictamente secuencial: cada bloque calibra antes del siguiente.

---

## Rúbrica de Verificación

### Correctness
- sqdmulh REDC produce output ∈ [0, p) para todo input en [0, p)
- Signed arithmetic contenida dentro del REDC — butterfly exterior sin cambios
- ilpFactor no cambia output numérico (solo scheduling)
- mu_tw precomputación es correcta: mu_tw[i] = tw[i] * mu mod 2^32
- lake build 0 errors, 0 new sorry

### Performance
- sqdmulh NEON mejora ≥30% sobre vmull NEON (instrucciones × lanes)
- ilpFactor=2 mejora ≥10% adicional (V0/V1 dual-issue)
- Scalar sin regresión (REDCMethod.vmullWidening para scalar)
- Cost model predice gain ±20% del real

### Quality
- No código duplicado (shared helpers, dispatch por REDCMethod)
- Dimensiones nuevas descubribles por cost model (no hardcoded)
- Cada dimensión tiene smoke test con native_decide
- Benchmark vs P3 real documentado

---

## Visión a Largo Plazo: SPIRAL Verificado

Lo que distingue este proyecto de Plonky3: cada optimización no es hardcodeada
sino **emergente del cost model parametrizado por hardware**.

```
SPIRAL:    SPL formulas → iterative search → autotuning empírico
Plonky3:   hardcoded Barrett + DIF + interleaving → manual per-target
TRZK:      E-graph rules → equality saturation → cost extraction → Lean proofs
```

Cuando cambie el hardware (RISC-V vector, AVX-512, ARM SVE2), Plonky3 reescribe.
TRZK re-extrae. Cada rewrite rule tiene un theorem de soundness:

```
fused(S₀, S₁) ≡ seq(S₀, S₁)   -- provable por composición de butterfly
REDC_vmull ≡ REDC_sqdmulh        -- provable por Montgomery correctness
interleave(bf₁,bf₂) ≡ seq(bf₁,bf₂)  -- trivially true (datos independientes)
```

El plan v3.5.0 es el primer paso hacia este objetivo: expandir el espacio de decisiones
del Plan manteniendo la rigurosidad formal del framework.

---

## v3.6.0 — Vectorizar Scalar Stages (halfSize < 4)

**Fecha de planificación**: 2026-04-08
**Prerequisito**: v3.5.0 completa (B35-5 finding: 2 scalar stages = 48% del NTT)
**Branch**: TBD

### Hallazgo que motiva esta fase

B35-5 profiling reveló que el bottleneck del NTT NEON NO es cache (como asumíamos)
sino 2 stages scalar que caen a fallback porque `halfSize < lanes` (4 para NEON).

```
BabyBear N=2^16:  SIMD stages (0-13) = 272μs (51.4%), Scalar stages (14-15) = 257μs (48.6%)
BabyBear N=2^20:  SIMD stages (0-17) = 9397μs (58.4%), Scalar stages (18-19) = 6696μs (41.6%)
```

Cada stage SIMD: ~19μs. Cada stage scalar: ~128μs (6.7× más lento).

Las opciones A (late merge), B (cache blocking), C (four-step NTT) evaluadas en B35-5
no atacan este bottleneck. La Opción D (vectorizar halfSize<4) sí.

### Plan de implementación

#### N36.1: `emitNeonButterflyDIT_HalfSize2_C` (FUNDACIONAL, 1-2 días)

Para halfSize=2: butterfly pairs `(data[i], data[i+2])` y `(data[i+1], data[i+3])`.

**Approach**: Cargar 4 elementos contiguos `[a0, a1, a2, a3]` en 1 registro NEON.
Los butterfly pairs son `(a0, a2)` y `(a1, a3)` — los elementos low `[a0, a1]` son
los "a" y los elementos high `[a2, a3]` son los "b". Split natural con
`vget_low_s32` / `vget_high_s32`.

```c
static inline void neon_bf_dit_hs2(int32_t* data_ptr, const int32_t* tw_ptr,
    const int32_t* mu_tw_ptr, int32x4_t p_vec_s, uint32x4_t p_vec) {
  // Load: 4 contiguous elements [a0, a1, b0, b1] where b = data+halfSize
  int32x4_t all = vld1q_s32(data_ptr);        // [a0, a1, a2, a3]
  int32x4_t tw4 = vld1q_s32(tw_ptr);          // [tw0, tw1, ?, ?]

  // Split: a=[a0,a1], b=[a2,a3] — natural low/high split, NO transpose needed
  // ... sqdmulh REDC on 4 lanes (2 butterflies in parallel) ...
  // NOTE: tw4 must have tw0 at [0], tw1 at [1] matching b0=[2], b1=[3]
  // This requires REDC to multiply b_half × tw_half — using 2-lane vmull or
  // restructuring so all 4 lanes have meaningful (b, tw) pairs.

  // Harvey reduce + recombine
  // Store: 4 elements back
  vst1q_s32(data_ptr, result);
}
```

**Detalle clave del REDC**: Para halfSize=2, hay dos butterflies independientes.
Si usamos sqdmulh REDC (4-lane), necesitamos que las 4 lanes contengan datos
válidos. Approach: cargar 4 b-values y 4 twiddles de 2 grupos de butterflies
consecutivos (no 2 del mismo grupo), hacer sqdmulh en 4 lanes, y store los
4 resultados a las posiciones correctas.

**Alternativa más simple**: procesar 2 grupos del outer loop en cada iteración.
Cada grupo tiene halfSize=2 → 2 butterflies → 4 b-values. Cargar los 4 b-values
de 2 grupos distintos, hacer sqdmulh × 4 lanes, Harvey × 4 lanes.

**Gate**: Compilación exitosa + output idéntico a scalar para BabyBear N=16,64,256.

#### N36.2: `emitNeonButterflyDIT_HalfSize1_C` (FUNDACIONAL, 1-2 días)

Para halfSize=1: butterfly pairs `(data[i], data[i+1])`. Datos almacenados como
pares contiguos `[a0, b0, a1, b1, a2, b2, a3, b3]`.

**Approach**: Cargar 4 elementos `[a0, b0, a1, b1]`, deinterleave con `vuzp` para
separar a's `[a0, a1]` y b's `[b0, b1]`, hacer 2 butterflies en paralelo con
sqdmulh REDC en 4 lanes (rellenando con datos de siguiente par si posible),
interleave con `vzip`, store.

```c
static inline void neon_bf_dit_hs1(int32_t* data_ptr, const int32_t* tw_ptr,
    const int32_t* mu_tw_ptr, int32x4_t p_vec_s, uint32x4_t p_vec) {
  // Load 4 consecutive: [a0, b0, a1, b1]
  int32x4_t packed = vld1q_s32(data_ptr);

  // Deinterleave: separate a's and b's
  // vuzp1_s32([a0,b0], [a1,b1]) = [a0, a1]
  // vuzp2_s32([a0,b0], [a1,b1]) = [b0, b1]
  int32x2_t lo = vget_low_s32(packed);   // [a0, b0]
  int32x2_t hi = vget_high_s32(packed);  // [a1, b1]
  int32x2_t a_half = vuzp1_s32(lo, hi);  // [a0, a1]
  int32x2_t b_half = vuzp2_s32(lo, hi);  // [b0, b1]

  // REDC product: tw * b — need full 4-lane register
  // Pack 2 butterfly pairs from adjacent groups into 4 lanes:
  int32x4_t b_vec = vcombine_s32(b_half, b_half2);  // [b0, b1, b2, b3]
  int32x4_t tw_vec = vld1q_s32(tw_ptr);             // [tw0, tw1, tw2, tw3]

  // sqdmulh REDC on 4 lanes (4 butterflies in parallel)
  // ... sqdmulh + canonicalize → wb_red[0..3] ...

  // Harvey reduce: sum = a + wb_red, diff = (a+p) - wb_red
  // ... 4 lanes ...

  // Reinterleave: [sum0, diff0, sum1, diff1]
  int32x2_t res_lo = vzip1_s32(sum_lo, diff_lo);  // [sum0, diff0]
  int32x2_t res_hi = vzip1_s32(sum_hi, diff_hi);  // [sum1, diff1]
  int32x4_t result = vcombine_s32(res_lo, res_hi);

  // Store 4 elements back
  vst1q_s32(data_ptr, result);
}
```

**Gate**: Compilación exitosa + output idéntico a scalar para BabyBear N=16,64,256.

#### N36.3: Modificar `emitStageC` para dispatch (CRÍTICO, 1 día)

Cuando `halfSize < lanes && halfSize >= 1`, usar la función correspondiente:

```lean
let isSIMD := bfUsed != "" && stage.radix != .r4 && halfSize >= lanes
let isSmallSIMD := halfSize < lanes && halfSize >= 1 && stage.radix != .r4
if isSIMD then
  -- existing SIMD path
else if isSmallSIMD then
  -- new: emit loop calling neon_bf_dit_hs2 or neon_bf_dit_hs1
  let bfSmall := if halfSize == 2 then "neon_bf_dit_hs2" else "neon_bf_dit_hs1"
  -- loop structure: process 2-4 groups per iteration
  ...
else
  -- scalar fallback (only for R4 now)
```

**Gate**: `lake build` exitoso, stages 14-15 ya no caen a scalar.

#### N36.4: Validación exhaustiva (PARALELO, 1 día)

1. Comparar output element-by-element contra Python reference:
   - BabyBear: N = 2^10, 2^12, 2^14, 2^16, 2^18, 2^20
   - KoalaBear: N = 2^10, 2^14, 2^16, 2^20
   - Mersenne31: N = 2^10, 2^14, 2^16
2. Verificar propiedad: output[i] < p para todo i (Harvey guarantee)
3. Verificar invertibilidad: NTT → iNTT = identity (si iNTT está implementado)
4. Registrar resultados en BENCHMARKS.md

**Gate**: 0 mismatches en todos los test vectors.

#### N36.5: Benchmark + calibración (ORIGINAL — SUPERSEDED por N36.5a/N36.5b)

> **NOTA**: Este bloque fue reemplazado después de que B36-1+B36-2 mostraron 0% gain
> a pesar de correctness confirmada. El profiler standalone (bench_per_stage.c) no era
> representativo del código generado monolítico. Ver N36.5a y N36.5b abajo.

~~1. Benchmark BabyBear N=2^16 y N=2^20, C NEON~~
~~2. Comparar contra v3.5.0 (con scalar stages) y P3-real~~
~~3. Per-stage profiling: confirmar que stages 14-15 ahora son ~19-30μs (no ~128μs)~~
~~4. Ajustar cost model si necesario: agregar `smallSIMDCost` a `Plan.totalCost`~~
~~5. Registrar en BENCHMARKS.md~~

~~**Gain esperado**: ~530μs → ~310-340μs para N=2^16 (~36-40% mejora).~~

---

### Post-B36-1/B36-2: El resultado inesperado y qué aprendimos

**Resultado**: N36.1-N36.4 completados exitosamente. 4/4 validaciones PASS, zero
mismatches. PERO: 264μs (v3.6.0 con hs2+hs1) vs 253μs (v3.5.0 sin ellos) = **~0% gain**.

**Por qué la predicción falló**: El profiler standalone (`bench_per_stage.c`) medía
funciones separadas compiladas independientemente. Cada stage era una función aislada
con `clock_gettime` alrededor. En ese contexto, los scalar stages (halfSize=2,1)
efectivamente tardaban ~128μs cada uno.

Pero el código generado real es **una función monolítica de ~1500 líneas** donde:
- Todas las butterflies son `static inline` → el compilador las inlinea
- Los 16 stages son bloques secuenciales DENTRO de una función → el compilador puede
  reordenar instrucciones entre stages
- El OoO engine del ARM solapa el final de un stage con el inicio del siguiente
- clang `-O2` puede auto-vectorizar los scalar loops (los reconoce como patterns)

El resultado: los "scalar stages" en el código generado probablemente NUNCA fueron
el bottleneck real. El compilador ya los optimizaba en el contexto monolítico.

**Lección fundamental para el proceso de fine-tuning**: Los microbenchmarks aislados
son útiles para calibrar costos de INSTRUCCIONES individuales (bench_redc_isolated.c
acertó en el ratio vmull/sqdmulh). Pero NO sirven para predecir bottlenecks a nivel
de STAGE porque no capturan las optimizaciones inter-stage del compilador.

Para predecir bottlenecks de stage, hay que medir DENTRO del código generado real.

---

#### N36.5a: CNTVCT Per-Stage Profiling (CRÍTICO, 1 día)

**Objetivo**: Medir el tiempo real de cada stage DENTRO del código generado monolítico,
usando ARM cycle counters con fence markers que preservan las optimizaciones intra-stage.

**Por qué CNTVCT y no clock_gettime**: La instrucción ARM `mrs x0, CNTVCT_EL0` lee
el contador de ciclos del sistema con:
- Overhead: 0.4 ns (bare) o 13.2 ns (con `isb` serialization barrier)
- Resolución: 41.7 ns en Apple Silicon (24 MHz), 10-20 ns en Graviton
- Para stages de ~15μs, el overhead de 13.2 ns es 0.09% — imperceptible

La combinación `isb` + `mrs` + clobber `memory` actúa como **optimization barrier**:
el compilador NO puede mover loads/stores a través de ella. Esto re-establece
boundaries de stage en el binario sin destruir las optimizaciones DENTRO de cada stage.

**Implementación**: Agregar flag `profiled : Bool := false` a `emitSIMDNTTC`.
Cuando `profiled = true`, emitir fence markers entre stages:

```c
void ntt_ultra_profiled(int32_t* data, const int32_t* twiddles, const int32_t* mu_tw) {
  uint64_t _ticks[17];  // 16 stages + 1 end marker

  // Constants (unchanged)
  uint32x4_t p_vec = vdupq_n_u32(2013265921U);
  int32x4_t p_vec_s = vdupq_n_s32((int32_t)2013265921U);
  // ...

  // Fence 0: start
  asm volatile("isb\nmrs %0, CNTVCT_EL0" : "=r"(_ticks[0]) :: "memory");

  /* Stage 0: SIMD sqdmulh (halfSize=32768, groups=1) */
  for (size_t grp = 0; grp < 1; grp++) {
    for (size_t pr = 0; pr < 32768; pr += 4) {
      // ... butterfly ...
    }
  }

  // Fence 1: end of stage 0
  asm volatile("isb\nmrs %0, CNTVCT_EL0" : "=r"(_ticks[1]) :: "memory");

  /* Stage 1: SIMD sqdmulh (halfSize=16384, groups=2) */
  // ...

  // Fence 16: end of stage 15
  asm volatile("isb\nmrs %0, CNTVCT_EL0" : "=r"(_ticks[16]) :: "memory");

  // Print timing (24 MHz on Apple Silicon — adjust for other platforms)
  uint64_t _freq = 24000000;
  double _total = 0;
  for (int _s = 0; _s < 16; _s++) {
    double _us = (double)(_ticks[_s+1] - _ticks[_s]) / _freq * 1e6;
    _total += _us;
    printf("  Stage %2d (hs=%5d): %7.2f us\\n", _s,
           /* halfSize for this stage */, _us);
  }
  printf("  Total: %.2f us\\n", _total);
}
```

**Overhead total**: 17 fence markers × 13.2 ns = 224 ns sobre ~253μs = **0.09%**.
La medición no distorsiona lo que mide.

**Tareas concretas**:

1. Agregar parámetro `profiled : Bool := false` a `emitSIMDNTTC` en SIMDEmitter.lean.
   Cuando true: emitir `uint64_t _ticks[numStages+1];` al inicio de la función.

2. En `emitStageC`: cuando `profiled = true`, emitir el fence marker
   `asm volatile("isb\\nmrs %0, CNTVCT_EL0" : "=r"(_ticks[{stageIdx}]) :: "memory");`
   ANTES de cada stage block.

3. Al final de la función (en `emitSIMDNTTC`): emitir el fence marker final + el
   loop de print.

4. En OptimizedNTTPipeline.lean: agregar flag `--profiled` que pasa `profiled := true`
   a `emitSIMDNTTC`.

5. Compilar y correr: `./ntt_bench --profiled` con BabyBear N=2^16 (200 iteraciones,
   promediar). Registrar la tabla de tiempos per-stage.

**Archivos a modificar**: `SIMDEmitter.lean` (emitSIMDNTTC, emitStageC),
  `OptimizedNTTPipeline.lean` (flag --profiled)
**Archivos a crear**: ninguno (se emite en el C generado)

**A qué resultados aspiramos y por qué**:

Esperamos ver UNO de tres patrones:

**Patrón 1: Distribución uniforme (~15-17μs por stage)**
```
Stage  0 (hs=32768): 17.1 us (6.8%)
Stage  1 (hs=16384): 16.8 us (6.6%)
...
Stage 14 (hs=    2): 15.9 us (6.3%)
Stage 15 (hs=    1): 15.5 us (6.1%)
Total: 253.0 us
```
**Significado**: El NTT ya está bien balanceado. Todos los stages cuestan lo mismo
porque el compilador optimiza eficientemente el código monolítico. No hay un
bottleneck localizado — mejorar requiere optimizar TODAS las butterflies (cambio
algorítmico) o reducir tráfico de memoria global (four-step NTT para N grande).

**Implicación**: El +64% vs P3-reference y ~253μs es cercano al óptimo para
esta arquitectura de codegen. Las ganancias marginales futuras vendrían de:
- Negacyclic twist merge (~5-8%)
- Four-step NTT para N=2^20 donde cache misses sí importan
- Otros primitivos (FRI fold, polynomial commitment)

**Patrón 2: Early stages lentos (stages 0-3 > 20μs, resto ~14μs)**
```
Stage  0 (hs=32768): 24.3 us (9.6%)
Stage  1 (hs=16384): 22.1 us (8.7%)
Stage  2 (hs= 8192): 19.8 us (7.8%)
Stage  3 (hs= 4096): 17.2 us (6.8%)
...
Stage 15 (hs=    1): 13.8 us (5.5%)
Total: 253.0 us
```
**Significado**: Cache misses en early stages (stride >> L1). El hardware prefetcher
mitiga parcialmente pero no elimina la penalty. Los early stages pagan ~40-70% más
que los late stages.

**Implicación**: Four-step NTT (Bailey's algorithm) es la siguiente optimización.
Descomponer N=65536 como 256×256 sub-NTTs que caben en L1. Gain estimado: ~15-20%
para N=2^16, mayor para N=2^20.

**Patrón 3: Un stage es outlier (2× o más que los demás)**
```
Stage  0 (hs=32768): 16.5 us (6.5%)
...
Stage  7 (hs=  256): 31.2 us (12.3%)  ← OUTLIER
...
Stage 15 (hs=    1): 15.1 us (6.0%)
Total: 270.0 us
```
**Significado**: Bug o ineficiencia localizada en un stage específico. Puede ser:
- Compilador genera código subóptimo para un tamaño de loop específico
- Alignment issue (datos no alineados a 16 bytes para vld1q)
- Branch misprediction en el loop del stage
- Transition entre butterfly functions (cambio de signature entre stages)

**Implicación**: Fix puntual de alto ROI. Investigar con `perf annotate` o
Instruments "CPU Counters" sobre ESE stage específico.

**Gate**:
1. Profiling compila y corre, produce tabla de 16 stages con tiempos en μs
2. Tiempos suman ≈ benchmark total (±5%)
3. Patrón identificado (1, 2, o 3)
4. Resultados registrados en BENCHMARKS.md con timestamp y configuración

---

#### N36.5b: Decision Gate — Siguiente optimización o pivot (HOJA, medio día)

**Objetivo**: Con datos reales de N36.5a, decidir la siguiente fase del proyecto.

**Decisión basada en el patrón observado**:

| Patrón | Próxima acción | Versión |
|--------|---------------|---------|
| **1 (uniforme)** | NTT cercano al óptimo para esta arch. Pivotar a: (a) negacyclic twist merge (5-8% gratis), (b) otros primitivos (FRI fold), (c) v3.7.0 verificación formal | v3.7.0 = verificación |
| **2 (early stages lentos)** | Four-step NTT (Bailey 256×256). Gain ~15-20% para N=2^16, más para N=2^20. | v3.7.0 = four-step NTT |
| **3 (outlier)** | Fix puntual + re-profile. Después decidir entre (1) y (2). | Fix en v3.6.1, luego re-evaluar |

**Reflexión sobre el proceso de fine-tuning**: N36.5b también debe documentar
las lecciones del proceso v3.5.0 → v3.6.0:

1. **Microbenchmarks aislados vs código generado monolítico**: El profiler standalone
   predijo un bottleneck que no existía en el código real. Los microbenchmarks
   de INSTRUCCIONES (bench_redc_isolated.c) sí fueron precisos. Los microbenchmarks
   de STAGES (bench_per_stage.c) no. La diferencia: el compilador optimiza inter-stage
   en código monolítico pero no puede hacerlo entre funciones separadas.

2. **El costo de optimizar sin medir correctamente**: N36.1-N36.3 implementaron
   código correcto pero sin gain. El esfuerzo no fue desperdiciado (el código es
   correcto y puede ser útil en otros contextos — por ejemplo, si se desactiva
   inlining con `__attribute__((noinline))`), pero el ROI fue 0% porque el
   diagnóstico era incorrecto.

3. **CNTVCT debería haber sido el PRIMER paso de B35-5**: Si hubiéramos instrumentado
   el código generado directamente en vez de crear un profiler standalone, habríamos
   visto la distribución real y evitado implementar hs2/hs1 sin gain. El profiler
   standalone era la herramienta incorrecta para la pregunta.

4. **El cost model calibrado (B35-2, B35-4) SÍ funcionó**: Las calibraciones de
   instrucciones individuales fueron precisas (sqdmulh ratio, ILP discount = 0).
   El fallo fue en la PREDICCIÓN de bottleneck, no en el cost model per se. Esto
   sugiere que el cost model necesita un componente de MEMORIA (cache misses,
   bandwidth) además del componente ALU que ya tiene.

**Documentar** en ARCHITECTURE.md:
- Datos de profiling CNTVCT per-stage
- Patrón observado
- Decisión para v3.7.0
- Lecciones del proceso v3.5.0 → v3.6.0

**Gate**:
1. Decisión documentada en ARCHITECTURE.md
2. Lecciones registradas (para que futuros ciclos de optimización eviten el mismo error)
3. Si se elige four-step NTT: DAG topológico para v3.7.0

### DAG (v3.6.0 actualizado)

```
N36.1 [FUND] ──→ N36.3 [CRIT] ──→ N36.4 [PAR] ──→ N36.5a [CRIT] ──→ N36.5b [HOJA]
N36.2 [FUND] ──┘                                       ↑
                                            (diagnosticar 0% gain)
```

N36.1-N36.4 completados. N36.5a es el diagnóstico con CNTVCT. N36.5b es la decisión.

### Verificación: Enfoque Pragmático (mismo nivel que SIMDEmitter existente)

**Decisión**: Los nuevos butterflies se emiten como strings C (Enfoque C del análisis
de verificación). Esto es consistente con cómo se implementó todo el SIMDEmitter
existente — `emitNeonButterflyBody`, `emitNeonButterflyDIT_Harvey_C`,
`emitNeonButterflyDIT_Sqdmulh_C` son TODOS string emission sin theorems.

**La frontera de verificación formal es el path scalar** (VerifiedPlanCodeGen →
TrustLean.Stmt → stmtToC). El SIMDEmitter completo está fuera de esta frontera.
Agregar los butterflies halfSize<4 como strings no degrada las garantías existentes.

**Validación empírica**:
- Element-by-element vs Python reference (N36.4)
- Property testing: output < p (N36.4)
- Invertibilidad NTT → iNTT (N36.4)

**La verificación formal del path SIMD se planifica para v3.7.0** (ver siguiente sección).

---

## v3.7.0 — Verificación Formal del Path SIMD via TrustLean.Stmt

**Fecha de planificación**: 2026-04-08
**Prerequisito**: v3.6.0 completa
**Objetivo**: Unificar los paths scalar y SIMD bajo el mismo framework verificado.

### Motivación

Hoy hay dos pipelines de codegen paralelos:

```
Path Verificado (scalar):
  VerifiedPlanCodeGen → Stmt → TrustLean.stmtToC → C scalar
  ↑ theorems: lowerReductionChoice_sound, etc.

Path No Verificado (SIMD):
  SIMDEmitter → String → C NEON
  ↑ zero theorems, validación empírica solamente
```

v3.7.0 unifica ambos: las instrucciones NEON se modelan como constructores de
`TrustLean.Stmt`, con semántica formal y traducción a C via `stmtToC`.

### Plan

#### 1. Extender TrustLean.Stmt con constructores NEON (~5-7 días)

Agregar al IR de TrustLean constructores que modelan instrucciones NEON relevantes:

```lean
-- En TrustLean/Stmt.lean (o Bridge/TrustLean.lean):
inductive Stmt where
  | ... -- existentes
  -- NEON vector operations (new):
  | neonLoad4 (dst : VarName) (ptr : LowLevelExpr)        -- vld1q_s32
  | neonStore4 (ptr : LowLevelExpr) (src : VarName)       -- vst1q_s32
  | neonTrn1 (dst src1 src2 : VarName)                    -- vtrn1q_s32
  | neonTrn2 (dst src1 src2 : VarName)                    -- vtrn2q_s32
  | neonUzp1 (dst src1 src2 : VarName)                    -- vuzp1_s32
  | neonUzp2 (dst src1 src2 : VarName)                    -- vuzp2_s32
  | neonZip1 (dst src1 src2 : VarName)                    -- vzip1_s32
  | neonZip2 (dst src1 src2 : VarName)                    -- vzip2_s32
  | neonSqdmulh (dst src1 src2 : VarName)                 -- vqdmulhq_s32
  | neonMul (dst src1 src2 : VarName)                     -- vmulq_s32
  | neonHsub (dst src1 src2 : VarName)                    -- vhsubq_s32
  | neonAdd (dst src1 src2 : VarName)                     -- vaddq_u32
  | neonSub (dst src1 src2 : VarName)                     -- vsubq_u32
  | neonCmpGe (dst src1 src2 : VarName)                   -- vcgeq_u32
  | neonAnd (dst src1 src2 : VarName)                     -- vandq_u32
  | neonBroadcast (dst : VarName) (val : Nat)             -- vdupq_n_s32
```

Cada constructor modela UNA instrucción NEON con semántica formal sobre
vectores de 4 elementos.

#### 2. Extender stmtToC para emitir NEON intrinsics (~2 días)

```lean
def stmtToC (indent : Nat) : Stmt → String
  | ... -- existentes
  | .neonLoad4 dst ptr =>
    pad indent ++ s!"int32x4_t {dst} = vld1q_s32({exprToC ptr});"
  | .neonSqdmulh dst s1 s2 =>
    pad indent ++ s!"int32x4_t {dst} = vqdmulhq_s32({s1}, {s2});"
  | .neonTrn1 dst s1 s2 =>
    pad indent ++ s!"int32x4_t {dst} = vtrn1q_s32({s1}, {s2});"
  -- etc.
```

#### 3. Reescribir butterflies como Stmt (~3-5 días)

```lean
def lowerHalfSize2ButterflyNeon (dataPtr twPtr muTwPtr : VarName)
    (p : Nat) (cgs : CodeGenState) : Stmt :=
  -- Load 4 contiguous elements
  let (allReg, cgs1) := cgs.freshVar
  let s1 := Stmt.neonLoad4 allReg (.varRef dataPtr)
  -- Split low/high
  let (aReg, cgs2) := cgs1.freshVar
  let (bReg, cgs3) := cgs2.freshVar
  let s2 := Stmt.neonGetLow aReg allReg
  let s3 := Stmt.neonGetHigh bReg allReg
  -- sqdmulh REDC on combined register
  -- ... (sequence of neonSqdmulh, neonMul, neonHsub for REDC) ...
  -- Harvey reduce
  -- ... (neonCmpGe, neonAnd, neonSub) ...
  -- Recombine and store
  Stmt.seq s1 (Stmt.seq s2 (Stmt.seq s3 ...))
```

#### 4. Probar soundness del butterfly NEON via Stmt (~5-7 días)

```lean
/-- The NEON halfSize=2 butterfly produces the same output as the scalar butterfly
    when applied to 4 contiguous elements paired as (0,2) and (1,3). -/
theorem lowerHalfSize2ButterflyNeon_sound
    (data : Array Int) (tw : Array Int) (p : Nat) (hp : 0 < p)
    (h_len : data.size ≥ 4) (h_tw : tw.size ≥ 2)
    (h_bound : ∀ i, i < 4 → 0 ≤ data[i]! ∧ data[i]! < p) :
    let result_neon := evalStmt (lowerHalfSize2ButterflyNeon ...) env
    let result_scalar := evalStmt (lowerScalarButterfly ...) env
    -- Element-wise equivalence mod p
    ∀ i, i < 4 → result_neon[i] % p = result_scalar[i] % p := by
  sorry -- TODO: prove in v3.7.0
```

El `sorry` se reemplaza con la prueba formal que conecta la semántica de las
instrucciones NEON con la semántica aritmética de la butterfly.

### Estimación total: ~3-4 semanas

| Tarea | Días | Prerequisito |
|-------|------|-------------|
| Extender TrustLean.Stmt | 5-7 | — |
| Extender stmtToC | 2 | Stmt extensions |
| Reescribir butterflies como Stmt | 3-5 | Stmt + stmtToC |
| Probar soundness | 5-7 | Todo lo anterior |
| **Total** | **15-21** | |

### Impacto

Después de v3.7.0, TODO el codegen NEON pasa por el path verificado:

```
Path Unificado:
  VerifiedPlanCodeGen → Stmt (con constructores NEON) → stmtToC → C NEON
  ↑ theorems: lowerReductionChoice_sound, lowerHalfSize2ButterflyNeon_sound, etc.
```

El SIMDEmitter se convierte en un wrapper que llama a `lowerStageVerified` (ahora
con NEON-awareness) y `stmtToC`. La string emission ad-hoc desaparece.

**Nota**: `stmtToC` sigue siendo TRUSTED (no probado). Pero ahora es el ÚNICO punto
de confianza, en vez de tener un path trusted (scalar) y un path no trusted (SIMD).
