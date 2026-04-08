# TRZK v3.5.0 — Optimizaciones Ad-Hoc en Equality Saturation: Q&A

**Fecha**: 2026-04-07
**Complemento de**: TRZK_filosofico.md

---

## Pregunta: ¿Qué optimizaciones "ad hoc" vamos a implementar en nuestra filosofía de equality saturation?

De la conversación completa y el plan v3.5.0, estas son las optimizaciones concretas:

## Las 4 optimizaciones y cómo se integran

### 1. sqdmulh Montgomery REDC (B35-1, MAYOR IMPACTO)

**Qué es**: Reemplazar nuestro REDC de producto (vmull widening, 2 lanes, ~20+ instrucciones) por el `vqdmulhq_s32` Montgomery (4 lanes, ~15 instrucciones). Es cómo se computa `tw × b mod p` — el producto de twiddle por dato.

**Cómo se integra**: Nueva dimensión `REDCMethod` en `NTTStage`:
```
inductive REDCMethod where
  | vmullWidening       -- actual: vmull_u32, 2 lanes, ~20 instrucciones
  | sqdmulhMontgomery   -- nuevo: vqdmulhq_s32, 4 lanes, ~15 instrucciones
```

El cost model evalúa ambos. Para NEON, sqdmulh gana (menos instrucciones, más lanes). Para scalar, vmull gana (no hay vqdmulhq en scalar). El e-graph tiene la regla:
```
REDC_vmull(tw, b, p, μ) ≡ REDC_sqdmulh(tw, b, p, μ_tw)
```
La extracción elige por cost model — no hardcodeado.

**Gain esperado**: ~1.7× en instrucciones de butterfly. Calibrar con benchmark real antes de confiar en el número.

**Orden**: Bloque 1 (después del benchmark honesto). Es el cambio más grande y habilita el siguiente.

---

### 2. ILP Interleaving (B35-3, SEGUNDO IMPACTO)

**Qué es**: Procesar 2 butterflies independientes por iteración del inner loop. ARM tiene 2 pipes ASIMD (V0 para multiplies, V1 para add/sub). Hoy V1 está idle ~60% del tiempo porque todas las instrucciones van serializadas por V0. Con 2 butterflies en vuelo, V0 trabaja en el REDC del butterfly B mientras V1 hace el add/sub del butterfly A.

**Cómo se integra**: Nueva dimensión `ilpFactor` en `NTTStage`:
```
structure NTTStage where
  ...
  ilpFactor : Nat := 1  -- 1 = actual, 2 = dual-butterfly
```

El emitter cambia el step del inner loop de `lanes` a `2*lanes` y emite 2 calls por iteración. El compilador C con `-O2` hace el instruction scheduling automáticamente — no necesitamos assembly. El cost model descuenta ~25% por dual-issue.

**Gain esperado**: 20-40% adicional (papers). Calibrar con benchmark.

**Orden**: Bloque 3 (después de calibrar sqdmulh). sqdmulh reduce la presión de registros, lo cual habilita tener 2 butterflies en vuelo sin spilling excesivo.

---

### 3. Negacyclic Twist Merge (diferido a decisión, BAJO COSTO)

**Qué es**: Para NTT negacyclic (trabaja en Z_p[X]/(X^n+1)), normalmente se pre-multiplica cada coeficiente por `g^i` antes del NTT. Este twist se puede absorber en los twiddle factors del primer stage: usar `ψ·ω^k` en vez de `ω^k`. Elimina un pass completo de N multiplicaciones.

**Cómo se integra**: Nueva dimensión `TwiddleMode` en `Plan`:
```
inductive TwiddleMode where
  | precomputed     -- tabla estándar
  | twistMerged     -- twist absorbido en stage 0
```

Zero cambios en el emitter — solo cambia qué valores hay en la tabla de twiddles. La regla algebraica es:
```
NTT(twist(data, g), ω) ≡ NTT(data, merge(ω, g))
```

**Gain esperado**: ~5-8% si el NTT es negacyclic. Solo aplica en ciertos contextos (polynomial commitment schemes).

**Orden**: Se puede hacer en cualquier momento. Depende de si nuestro NTT necesita ser negacyclic.

---

### 4. Stage Merging / Blocking (B35-5, DECISIÓN GATE)

**Qué es**: Para los late stages del NTT (halfSize ≤ 32), cargar un bloque de 64 elementos en 16 NEON registers, procesar 5-6 stages sin volver a memoria, y store una vez al final. Elimina 5 store/load roundtrips.

**Cómo se integra**: Nueva dimensión `BlockingConfig` en `Plan`:
```
structure Plan where
  ...
  blockingFrom : Option Nat := none  -- si some L, stages L..end se fusionan
  blockSize : Nat := 64              -- elementos por bloque
```

La regla de equivalencia:
```
seq(Stage_L, ..., Stage_N) ≡ BlockedStages(L, N, blockSize)
```

El cost model evalúa: `shuffleCost` (trn_4x4 transposes) vs `loadStoreCost` (memory roundtrips).

**Gain esperado**: ~15-20% en los stages fusionados, que representan ~40% del NTT = ~6-8% neto.

**Orden**: Bloque 5 es solo una **decisión gate** — no implementamos stage merging en v3.5.0. Después de medir sqdmulh + ILP, si los late stages siguen siendo >25% del tiempo total, se planifica como v3.6.0. Si no, se difiere.

---

## Resumen del orden y gains acumulativos

| Paso | Optimización | Dimensión nueva | Gain estimado | Acumulado |
|------|-------------|----------------|---------------|-----------|
| **B35-0** | Benchmark honesto vs P3 real | — | baseline | — |
| **B35-1** | sqdmulh REDC | `REDCMethod` | ~1.7× butterfly | ~1.7× |
| **B35-2** | Calibrar cost model | — | ajuste | — |
| **B35-3** | ILP interleaving | `ilpFactor` | +20-40% | ~2.1-2.4× |
| **B35-4** | Calibrar cost model | — | ajuste | — |
| **B35-5** | Decisión stage merging | `BlockingConfig` (evaluación) | decidir | — |

**Nota importante**: los gains son estimaciones teóricas basadas en conteo de instrucciones y papers. El approach incremental con calibración en B35-2 y B35-4 nos da los números reales antes de comprometernos con el siguiente paso. Si sqdmulh da menos del 30% esperado, ajustamos el cost model antes de implementar ILP. Si ILP da menos del 10%, reconsideramos stage merging.

---

## Pregunta: ¿Cómo dependen estas optimizaciones del hardware target? ¿Cómo aparece esa dependencia en la saturación/extracción?

Cada optimización tiene un perfil hardware distinto. La dependencia se manifiesta en dos lugares: las **reglas coloreadas** (qué equivalencias son válidas bajo qué hardware) y el **cost model parametrizado** (cuánto cuesta cada alternativa en cada target).

## Cómo cada dimensión depende del hardware

### REDCMethod

| Target | vmullWidening | sqdmulhMontgomery | Ganador |
|--------|--------------|-------------------|---------|
| **ARM NEON** | 2 lanes, ~20 instr (vmull_u32 widening a uint64x2_t) | 4 lanes, ~15 instr (vqdmulhq_s32 nativo) | **sqdmulh** |
| **ARM scalar** | Funciona (emulado con mul64+shift) | NO existe vqdmulhq en scalar — sería emulado como `(2*a*b)>>32` con mul64, MÁS caro | **vmull** |
| **x86 AVX2** | 8 lanes via vpmuludq (widening eficiente, hardware nativo) | No hay equivalente directo de sqdmulh; se emula con vpmulhw (16-bit) o vpmuludq+shift | **vmull** (probablemente) |
| **FPGA** | Multiplicadores 64-bit baratos en DSP slices | Sin relevancia (no hay "instrucciones NEON") | **vmull** |

La instrucción `vqdmulhq_s32` es específica de ARM NEON. En otros targets no existe o es más cara que la alternativa. Por eso no se hardcodea — el cost model decide.

### ILPFactor

| Target | ilpFactor=1 | ilpFactor=2 | Ganador |
|--------|------------|------------|---------|
| **ARM NEON (OoO, 2 pipes)** | V1 idle 60% | V0+V1 dual-issue | **ilp=2** |
| **ARM scalar (OoO, 3 ALU)** | Ya hay ILP natural en scalar (3 ALU ports) | Marginal benefit, más loop overhead | **ilp=1** |
| **x86 AVX2 (OoO, 6 ports)** | Compiler already schedules well | ilp=2 o 4 podría ayudar | **ilp=2-4** (calibrar) |
| **FPGA (pipeline, no OoO)** | Pipeline depth > ILP | ilpFactor irrelevante | **ilp=1** |
| **ARM in-order (Cortex-A55)** | Sin OoO, todo serializado | ilp=2 ayuda más que en OoO (esconde latencia manualmente) | **ilp=2** |

ILP depende de: (1) cuántos pipes tiene el target, (2) si es out-of-order, (3) presión de registros (más ILP = más registros usados).

### BlockingConfig

| Target | Sin blocking | blockingFrom=10 | Ganador |
|--------|-------------|-----------------|---------|
| **ARM NEON (32 regs)** | 16 store/load roundtrips | 6 stages fusionados, 16 data regs | **blocking** |
| **x86 AVX2 (16 regs)** | Menos roundtrips | Solo 8 data regs = 32 elementos = 4 stages | **blocking parcial** |
| **x86 AVX-512 (32 regs)** | — | 16 data regs × 16 lanes = 256 elementos | **blocking agresivo** |
| **ARM scalar (31 GP regs)** | — | GP regs no son vectoriales, blocking ineficiente | **sin blocking** |

La profundidad de blocking depende directamente de `hw.numRegisters` y `hw.simdLanes`.

### TwiddleMode

| Target | Dependencia hardware |
|--------|---------------------|
| Todos | **Ninguna** — solo algebraico. `NTT(twist(d,g),ω) ≡ NTT(d,merge(ω,g))` es una identidad matemática, no depende del hardware. El cost model siempre prefiere `twistMerged` porque ahorra N multiplicaciones gratis. |

---

## Cómo aparece en la saturación/extracción

### En la saturación (colored e-graphs)

El sistema de colores que ya existe (HardwareColors.lean) define una jerarquía:
```
Root (color 0): reglas universales (válidas en todo hardware)
├── Scalar (color 1)
├── SIMD (color 2)
│   ├── NEON (color 3)
│   └── AVX2 (color 4)
```

Las reglas de equivalencia de REDCMethod se registran como **reglas coloreadas**:

```lean
-- Bajo color NEON: sqdmulh es equivalente a vmull
coloredRule (color := neon):
    REDC_vmull(tw, b, p, μ) ≡ REDC_sqdmulh(tw, b, p, μ_tw)

-- Bajo color Root (universal): la equivalencia semántica es la misma,
-- pero el cost model elige distinto según el target
```

Durante la saturación, `coloredStep` (MultiRelMixed.lean:175-186) merge los nodos equivalentes **solo bajo el color activo**. El base graph no se modifica — los merges viven en la `ColoredLayer` (delta union-find). Esto significa que el e-graph mantiene ambas alternativas simultáneamente.

### En la extracción

La extracción sucede en `coloredCostAwareExtractF` (ColoredExtraction.lean:69-72):

```lean
def coloredCostAwareExtractF (hw : HardwareCost) (state : State)
    (rootId : EClassId) (targetColor : ColorId) : Option MixedExpr :=
  -- 1. Crear vista temporal: merge los nodos que son equivalentes bajo targetColor
  let coloredGraph := applyColoredMerges state.baseGraph state.coloredLayer targetColor
  -- 2. Extraer la expresión más barata usando el cost model del hardware
  costAwareExtractF hw coloredGraph rootId 50 50
```

Cuando se extrae para NEON (color 3):
- `REDC_vmull` y `REDC_sqdmulh` están en la misma e-class (mergeados bajo color NEON)
- `costAwareExtractF` evalúa ambos con `mixedOpCost arm_neon_simd`:
  - vmull: `4 * hw.mul64 + ...` = ~20 ciclos
  - sqdmulh: `2 * hw.mul32 + hw.sub + 3` = ~7 ciclos
- **Elige sqdmulh** porque es más barato

Cuando se extrae para scalar (color 1):
- La misma e-class, pero ahora con `arm_cortex_a76`:
  - vmull: ~7 ciclos (mul64 es nativo en scalar)
  - sqdmulh: ~10 ciclos (emulado sin instrucción nativa)
- **Elige vmull** porque sqdmulh no tiene hardware nativo

**Un solo e-graph saturado → N extracciones distintas por hardware.** Esto es exactamente la visión "1 saturación + N extracciones" que los colored e-graphs habilitan. Hoy hacemos N runs separados, pero la infraestructura para hacerlo en 1 run ya existe (ColoredEGraph.lean, compositeFind, applyColoredMerges).

### Para ILP y Blocking

Estas dimensiones operan a nivel de **schedule** (Plan), no de **expresión** (MixedExpr). No son reglas del e-graph aritmético — son reglas del e-graph de schedule que evaluamos en `Plan.totalCost`:

```lean
-- En Plan.totalCost (NTTPlan.lean):
let ilpDiscount := if stage.ilpFactor > 1 && hw.isSimd
  then rawCost * 3 / 4   -- ~25% discount por dual-issue
  else rawCost            -- sin descuento para scalar

let blockingDiscount := if isInBlock stage plan.blockingFrom
  then shuffleCostPerStage hw   -- barato: ~2-4 ciclos de shuffles
  else loadStoreCostPerStage hw  -- caro: ~8-12 ciclos de memory roundtrip
```

Los parámetros `hw.isSimd`, `hw.simdLanes`, `hw.numRegisters` (que hoy no existe pero se agregaría) controlan qué combinaciones son viables. `generateCandidates` produce planes con diferentes combinaciones y `selectPlan` elige el más barato por cost model.

**La dependencia del hardware NO está hardcodeada en el código** — fluye a través del `HardwareCost` parametrizado. Si mañana ARM introduce SVE2 con 512-bit vectors y 64 registros, solo hay que agregar un `HardwareCost` nuevo y el framework re-extrae automáticamente el plan óptimo para ese target.
