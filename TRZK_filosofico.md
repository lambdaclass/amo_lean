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
