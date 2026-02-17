# AMO-Lean v2.0.0 — Plan de Migración a Lean 4.26

**Identificador**: amo-lean_v2.0.0
**Fase**: Fase 9 (Migración y Robustecimiento)
**Branch**: `feature/lean-4.26-upgrade`
**Main**: INTOCABLE hasta validación completa
**Fuente de verdad**: ESTE ARCHIVO

---

## Contexto

| Campo | Valor |
|-------|-------|
| Versión actual | Lean 4.16.0, Mathlib v4.16.0 |
| Versión objetivo | Lean 4.26.0, Mathlib v4.26.0 |
| LOC | 36,326 (84 archivos Lean) |
| Axiomas | 9 |
| Sorry | 12 (Poseidon, limitación match splitter) |
| Tests | 2,850+ (0 fallos) |
| Módulos | 2,647 compilando |
| Complejidad | HIGH |
| Dominio | lean4 |

### Objetivo principal

Migrar amo-lean a Lean 4.26 para:
1. Unificar toolchain con vr1cs-lean
2. Habilitar port del motor de e-graphs verificado (5,000 LOC, 250 teoremas, 0 sorry)
3. Acceder a mejoras de Lean 4.26 (grind, parallel elaboration, mejor omega)
4. Preparar base para amo-lean v2.0.0

### Prioridad absoluta

**NO ROMPER la versión existente.** Main intocable. Todo en branch. Gate obligatorio entre subfases.

---

## Bibliografía relevante

- egg: Fast and Extensible Equality Saturation (Willsey 2021, POPL)
- HEC: Equivalence Verification Checking via E-Graphs (Yin 2025)
- Formally Verified NTT (Trieu 2025, Rocq)
- AMO-Lean: Ruta de Trabajo hacia zkVM (roadmap interno)
- eqsat: Equality Saturation Dialect for MLIR (Merckx 2025)

## Lecciones aplicables (de vr1cs-lean)

| ID | Lección | Impacto en migración |
|----|---------|---------------------|
| L-199 | `native_decide` + proof fields = free variables error | Verificar campos Goldilocks/BabyBear |
| L-200 | HashMap.fold NO tiene induction principle en v4.26 | Reescribir como recursión sobre toList |
| L-207 | `by_contra` no existe sin Mathlib en v4.26 | Buscar usos, reemplazar con rcases |
| L-209 | `attribute [local irreducible]` ANTES de docstring | Revisar e-graph con matches complejos |
| L-300 | Docstrings antes de `section` causan parse error | Auditar todos los section blocks |
| L-302 | Port entre versiones: adaptar namespace, no copiar | Aplicar al port del e-graph verificado |

---

## Baseline pre-migración (preservar)

| Métrica | Valor v1.1.0 | Gate v2.0.0 |
|---------|-------------|-------------|
| `lake build` | 0 errores | 0 errores |
| Módulos compilados | 2,647 | >= 2,647 |
| Axiomas | 9 | <= 9 |
| Sorry | 12 | <= 12 |
| Tests #eval | 156+ bloques | Todos pasan |
| NTT oracle tests | 64/64 | 64/64 |
| Poseidon test vectors | 21/21 | 21/21 |

---

## Estrategia de rollback y checkpoints

### Tags de progreso
- Tras Subfase 2 completada: `git tag v2.0.0-alpha1-foundation`
- Tras Subfase 4 completada: `git tag v2.0.0-alpha2-ntt`
- Tras Subfase 7 completada: `git tag v2.0.0-rc1`
- Tras Subfase 8 completada: `git tag v2.0.0`

### Criterio de abort
Si cualquier subfase toma >3x el tiempo estimado:
1. Evaluar si Lean 4.20 como stepping stone reduce el problema
2. Si no, evaluar backport parcial (traer solo e-graph verificado a v4.16)
3. Decisión conjunta antes de continuar

### Escape hatch
Si el primer `lake build` diagnóstico produce >300 errores no triviales (no solo import renames):
reevaluar con stepping stone 4.16 → 4.20 → 4.26.

---

## DAG de dependencias (orden topológico)

```
Capa 0 (FOUNDATIONAL):
  Basic.lean ← Field/Goldilocks ← Field/BabyBear
              ← NTT/Field ← Vector/Basic ← Matrix/Basic

Capa 1 (CRITICAL):
  EGraph/Basic [BLOCKER: Std.HashMap/HashSet]
  NTT/RootsOfUnity ← NTT/Properties
  Sigma/Basic

Capa 2 (PARALLEL):
  ┌─ EGraph/EMatch → Saturate → Optimize → VecExpr → Vector
  ├─ NTT/CooleyTukey → Correctness → Radix4/*
  ├─ FRI/Fold → Hash → Protocol → Prover → Verifier
  └─ Protocols/Poseidon/* → DomainSeparation

Capa 3 (INTEGRATION):
  Sigma/CodeGen, Sigma/Expand
  Backends/CCodeGen, Backends/Rust
  Verification/AlgebraicSemantics (5,739 LOC) ← RIESGO CONCENTRADO
  Verification/Poseidon_Semantics (12 sorry)

Capa 4 (ROOT):
  AmoLean.lean (raíz)
  Tests/*, Benchmarks/*
```

---

## Estimaciones de tiempo

| Subfase | Estimación | Varianza | Factor principal |
|---------|-----------|----------|-----------------|
| S1: Infraestructura | 1-2 horas | Baja | Mecánico |
| S2: Fundacional | 4-8 horas | Media | Goldilocks/BabyBear proofs |
| S3: E-Graph | 4-6 horas | Media | HashMap API |
| S4: NTT | 8-16 horas | **Alta** | BigOperators/Finset renames |
| S5: FRI + Protocolos | 6-12 horas | Media | 12 sorry Poseidon |
| S6: Integración | 6-12 horas | **Alta** | AlgebraicSemantics.lean (5,739 LOC) |
| S7: Tests | 2-4 horas | Baja | Mecánico |
| S8: Port E-Graph | 16-32 horas | **Alta** | Adaptación de tipos |
| **TOTAL** | **47-92 horas** | — | **6-12 días de trabajo** |

---

## Plan de trabajo (orden topológico)

### Fase 9 Subfase 1: Infraestructura
**Tipo**: FOUNDATIONAL | **Ejecución**: SECUENCIAL | **Est.**: 1-2h

| # | Tarea | Archivo(s) | Riesgo |
|---|-------|-----------|--------|
| 1.1 | Crear branch `feature/lean-4.26-upgrade` desde main | git | Ninguno |
| 1.2 | Actualizar `lean-toolchain` a v4.26.0 | lean-toolchain | N/A |
| 1.3 | Actualizar Mathlib rev en `lakefile.lean` a v4.26.0 | lakefile.lean | Bajo |
| 1.4 | Ejecutar `lake update` para resolver Mathlib v4.26.0 | lake-manifest.json | ALTO |
| 1.5 | Crear archivo canary `Tests/Canary426.lean` | Tests/Canary426.lean | Diagnóstico |
| 1.6 | Primer `lake build` — capturar TODOS los errores | — | Diagnóstico |
| 1.7 | Clasificar errores por categoría y módulo | — | Mapa de trabajo |

**GATE 1**: `lake update` exitoso + canary compila + lista de errores clasificada

**Decisión D4 revisada (QA-C3)**: Mantener `lakefile.lean` durante la migración. El bloque `script "phase0-test"` contiene código IO imperativo que no es expresable en TOML. Convertir a `lakefile.toml` solo después de Subfase 7, como tarea de limpieza.

**Archivo canary** (de-risk imports antes de tocar código real):
```lean
-- Tests/Canary426.lean — Verifica que todos los imports críticos resuelven en 4.26
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

#check Nat.Prime
#check ZMod
#check Finset.sum
```

---

### Fase 9 Subfase 2: Capa Fundacional
**Tipo**: FOUNDATIONAL | **Ejecución**: SECUENCIAL (firewall _aux) | **Est.**: 4-8h
**Depende de**: Subfase 1

**DE-RISK OBLIGATORIO antes de empezar** (QA-C2, QA-R3):
- Verificar que `Nat.strongRecOn` compila en 4.26 (afecta zpowMod en Goldilocks)
- Verificar que `Batteries.Data.UInt` resuelve (QA-C4; si no, buscar en `Init.Data.UInt`)
- Verificar `termination_by` syntax: 3 archivos usan `termination_by varname => expr` (deprecado; nuevo: `termination_by expr`)

| # | Tarea | Archivo(s) | Breaking changes esperados |
|---|-------|-----------|---------------------------|
| 2.1 | Migrar `Basic.lean` (AST, denotación) | AmoLean/Basic.lean | structure extends syntax, `termination_by` arrow |
| 2.2 | Migrar `Field/Goldilocks.lean` | AmoLean/Field/Goldilocks.lean | ZMod API, Batteries.UInt, Nat.strongRecOn |
| 2.3 | Migrar `Field/BabyBear.lean` | AmoLean/Field/BabyBear.lean | Mismo que Goldilocks |
| 2.4 | Migrar `NTT/Field.lean` | AmoLean/NTT/Field.lean | Mathlib imports |
| 2.5 | Migrar `Vector/Basic.lean` | AmoLean/Vector/Basic.lean | Vector ya no extiende Array (v4.21) |
| 2.6 | Migrar `Matrix/Basic.lean` | AmoLean/Matrix/Basic.lean | Imports Mathlib |

**GATE 2**: `lake env lean AmoLean/Basic.lean` + `lake env lean AmoLean/Field/Goldilocks.lean` + `lake env lean AmoLean/Field/BabyBear.lean` sin errores

**Estrategia por breaking change**:
- `structure S extends P : T` → `structure S : T extends P` (v4.18, buscar y reemplazar)
- `termination_by e => sizeOf e` → `termination_by sizeOf e` (v4.17+, 3 archivos)
- `Batteries.Data.UInt` → verificar; si falla, buscar en `Init.Data.UInt`
- `native_decide` → misma API pero verificar proof fields (L-199)
- Lucas primality → verificar import path `Mathlib.NumberTheory.LucasPrimality`

---

### Fase 9 Subfase 3: Motor E-Graph
**Tipo**: CRITICAL | **Ejecución**: SECUENCIAL (firewall _aux) | **Est.**: 4-6h
**Depende de**: Subfase 2
**BLOCKER**: Std.HashMap/HashSet → nueva API (QA-B1, B2)

**DE-RISK OBLIGATORIO**: Antes de empezar, inventariar TODOS los usos de HashMap/HashSet API en los 5+ archivos EGraph. Cross-referenciar con vr1cs-lean `EGraph/Core.lean` (ya compila en 4.26).

| # | Tarea | Archivo(s) | Breaking changes |
|---|-------|-----------|-----------------|
| 3.1 | Inventario HashMap/HashSet API | EGraph/*.lean | Diagnóstico |
| 3.2 | Migrar `EGraph/Basic.lean` (552 LOC) | AmoLean/EGraph/Basic.lean | Std.HashMap → nueva API, HashSet → Array |
| 3.3 | Migrar `EGraph/EMatch.lean` (396 LOC) | AmoLean/EGraph/EMatch.lean | partial functions, imports |
| 3.4 | Migrar `EGraph/Saturate.lean` (223 LOC) | AmoLean/EGraph/Saturate.lean | Imports |
| 3.5 | Migrar `EGraph/Optimize.lean` (495 LOC) | AmoLean/EGraph/Optimize.lean | Imports, partial |
| 3.6 | Migrar `EGraph/VerifiedRules.lean` (418 LOC) | AmoLean/EGraph/VerifiedRules.lean | ring tactic, Int lemmas |
| 3.7 | Migrar `EGraph/VecExpr.lean` (734 LOC) | AmoLean/EGraph/VecExpr.lean | Std.HashMap/HashSet |
| 3.8 | Migrar `EGraph/Vector.lean` (752 LOC) | AmoLean/EGraph/Vector.lean | Std.HashMap/HashSet |

**GATE 3**: Todos los archivos EGraph/ compilan individualmente + `#eval` tests del e-graph pasan

**Estrategia HashMap/HashSet**:
1. Verificar si `import Std.Data.HashMap` resuelve en 4.26; si no, determinar nuevo path
2. `Std.HashMap.empty` → `Std.HashMap.ofList []` o `.emptyWithCapacity n`
3. `HashMap.find?` → verificar si ahora es `HashMap.get?`
4. `Std.HashSet` en structs → evaluar reemplazo por `Array` (restricción universo, QA-L-F9-009)
5. Usar `_aux` para cada struct modificado, verificar antes de reemplazar
6. NO tocar VerifiedRules hasta que las estructuras compilen

---

### Fase 9 Subfase 4: Pipeline NTT
**Tipo**: CRITICAL | **Ejecución**: SECUENCIAL (cadena de dependencias larga) | **Est.**: 8-16h
**Depende de**: Subfase 2

| # | Tarea | Archivo(s) | Notas |
|---|-------|-----------|-------|
| 4.1 | NTT/RootsOfUnity.lean | Mathlib Finset, BigOperators |
| 4.2 | NTT/Properties.lean | Finset, proofs sensibles |
| 4.3 | NTT/Bounds.lean | omega, linarith |
| 4.4 | NTT/CooleyTukey.lean | Core algorithm |
| 4.5 | NTT/Correctness.lean | Proofs E2E |
| 4.6 | NTT/BabyBear.lean | native_decide, partial |
| 4.7 | NTT/ListFinsetBridge.lean | Bridge lemmas |
| 4.8 | NTT/Phase3Proof.lean | Heavy proofs |
| 4.9 | NTT/Radix4/*.lean (3 files) | 8 axiomas (interface) |
| 4.10 | NTT/*.lean restantes (~13 files) | Misc |

**GATE 4**: `lake env lean AmoLean/NTT/Correctness.lean` sin errores

**Riesgo principal**: Mathlib BigOperators/Finset renames. Verificar:
- `Mathlib.Algebra.BigOperators.Group.Finset.Basic` → ¿mismo path?
- `Finset.sum_congr`, `Finset.sum_comm` → ¿misma signatura?
- `open BigOperators` → ¿misma notación `∑`?

---

### Fase 9 Subfase 5: FRI + Protocolos
**Tipo**: PARALLEL | **Ejecución**: PARALLEL (FRI || Poseidon) | **Est.**: 6-12h
**Depende de**: Subfase 4

| Bloque | Archivos | Notas |
|--------|----------|-------|
| FRI (15 files) | FRI/*.lean | partial functions, Finset |
| Poseidon (9 files) | Protocols/Poseidon/*.lean | 12 sorry existentes, DomainSeparation |

**GATE 5**: Todos los FRI/ y Protocols/ compilan + sorry count <= 12 (no aumentan)

---

### Fase 9 Subfase 6: Integración
**Tipo**: PARALLEL | **Ejecución**: MIXTA (Sigma/Backends en paralelo, AlgebraicSemantics secuencial) | **Est.**: 6-12h
**Depende de**: Subfases 3, 4, 5

| Bloque | Archivos | Notas |
|--------|----------|-------|
| Sigma (5 files) | Sigma/*.lean | partial en CodeGen/Expand |
| Backends (3 files) | Backends/*.lean | String API changes (v4.26), code gen |
| **AlgebraicSemantics** | Verification/AlgebraicSemantics.lean | **DEDICADO** — 5,739 LOC, 914 simp, 14 maxHeartbeats |
| Verification rest (5 files) | Verification/*.lean restantes | Poseidon_Semantics (12 sorry) |

**GATE 6**: `lake build` COMPLETO (primer build exitoso de todo el proyecto)

**AlgebraicSemantics.lean — tratamiento especial** (QA-C6):
- 914 invocaciones de `simp` → si lemma names cambiaron, cascada de errores
- 14 `set_option maxHeartbeats` (hasta 12,800,000) → simp más lento en 4.26 puede requerir ajuste
- Estrategia: reemplazar `simp` por `simp only [...]` en proofs de alto heartbeat ANTES de migrar
- Si intractable: elevar heartbeat limit como workaround temporal, marcar como deuda técnica

---

### Fase 9 Subfase 7: Tests + Benchmarks + Validación + Cleanup
**Tipo**: LEAF | **Ejecución**: PARALLEL | **Est.**: 2-4h
**Depende de**: Subfase 6

| # | Tarea | Verificación |
|---|-------|-------------|
| 7.1 | Migrar Tests/*.lean | Todos los #eval pasan |
| 7.2 | Migrar Benchmarks/*.lean | Todos compilan |
| 7.3 | Ejecutar test suite completa | 2,850+ tests, 0 fallos |
| 7.4 | Verificar métricas baseline | axiomas <= 9, sorry <= 12 |
| 7.5 | Compilar y ejecutar tests C/Rust | Oracle tests 64/64 |
| 7.6 | Convertir `lakefile.lean` → `lakefile.toml` | Mover script a `scripts/phase0_test.sh` |
| 7.7 | Actualizar CLAUDE.md (toolchain, config) | Documentación |
| 7.8 | Tag `v2.0.0-rc1` | Git |

**GATE 7 (RELEASE GATE)**: TODAS las métricas baseline cumplidas. Branch listo para merge o para Subfase 8.

---

### Fase 9 Subfase 8: Port del motor E-Graph verificado
**Tipo**: CRITICAL | **Ejecución**: SECUENCIAL | **Est.**: 16-32h
**Depende de**: Subfase 7 (branch estable en 4.26)

Subdividido en 5 etapas (QA-Q6):

#### S8a: Port implementación (UnionFind + Core) — COMPLETADA
| # | Tarea | Origen (vr1cs-lean) | LOC | Estado |
|---|-------|---------------------|-----|--------|
| 8.1 | Port UnionFind (43 teoremas, zero sorry) | EGraph/UnionFind.lean | 1,235 | ✓ |
| 8.2 | Port Core structs (EClass, ENode, EGraph) | EGraph/Core.lean | 252 | ✓ |

#### S8b: Port invariantes estructurales — COMPLETADA
| 8.3 | Port CoreSpec (78 teoremas, zero sorry) | EGraph/CoreSpec.lean | 1,368 | ✓ |

#### S8a+ (bonus): Port operacional sin deps VR1CS — COMPLETADA
| 8.A | EMatch (pattern matching, instantiate) | EGraph/EMatch.lean | 201 | ✓ |
| 8.B | Saturate (fixpoint loop) | EGraph/Saturate.lean | 70 | ✓ |
| 8.C | ILP data model | EGraph/ILP.lean | 185 | ✓ |
| 8.D | ILP encoding (TENSAT) | EGraph/ILPEncode.lean | 233 | ✓ |
| 8.E | ILP solver (B&B + HiGHS) | EGraph/ILPSolver.lean | 314 | ✓ |
| 8.F | ParallelMatch (IO.asTask) | EGraph/ParallelMatch.lean | 209 | ✓ |
| 8.G | ParallelSaturate (threshold) | EGraph/ParallelSaturate.lean | 125 | ✓ |

**Resultado S8a-S8b+**: 10 archivos, 4,192 LOC, 121 teoremas, zero sorry, BUILD 3129 jobs OK

#### S8c: Port soundness semántica — BLOQUEADA por VR1CS domain types
| 8.4 | SemanticSpec (necesita VR1CS.Basic, Rules.SoundRule) | EGraph/SemanticSpec.lean | 2,061 | bloqueada |
| 8.5 | TranslationValidation (necesita VR1CS.Basic) | EGraph/TranslationValidation.lean | 278 | bloqueada |

#### S8d: Adaptación de tipos (LA PARTE DIFÍCIL)
| 8.6 | Adaptar `CircuitExpr p` → `Expr α` o crear typeclass genérico | — | ~500 est. |
| 8.7 | Port SoundRewriteRule pattern | Rules/SoundRule.lean | ~100 |
| 8.8 | Migrar 19 reglas existentes al nuevo pattern | EGraph/VerifiedRules.lean | ~400 |
| 8.X | Port SemanticSpec + TranslationValidation (desbloqueados por 8.6+8.7) | — | 2,339 |

#### S8e: Actualizar consumidores downstream
| 8.9 | Port Basic, ILPCheck, ILPSpec, Optimize (deps VR1CS) | EGraph/*.lean | ~700 |
| 8.10 | Port ExtendedOps (deps VR1CS.Extended) | EGraph/ExtendedOps.lean | 312 |
| 8.11 | Actualizar VecExpr, Vector | EGraph/VecExpr,Vector.lean | ~1,500 |

**GATE 8**: Motor e-graph con proofs formales, `lake build` sin errores, 0 sorry nuevos

**Decisión clave S8d**: ¿Generalizar a typeclass o probar de nuevo para `Expr α`?
- Opción A: Crear `class EGraphExpr (E : Type)` que abstraiga eval, constructores → proofs genéricos
- Opción B: Probar soundness de nuevo específicamente para `Expr α`
- **Ahora tenemos visibilidad clara**: 10/17 archivos portados sin problemas. Los 7 restantes dependen de VR1CS.Basic (CircuitExpr), VR1CS.Rules.SoundRule, VR1CS.CostModel, VR1CS.Extended.
- **Recomendación**: Opción A (typeclass) es más elegante pero requiere ~2x esfuerzo. Opción B es pragmática y suficiente para el objetivo de amo-lean.

---

## Registro de riesgos (actualizado post-QA)

| Riesgo | Prob. | Impacto | Mitigación |
|--------|-------|---------|-----------|
| Mathlib API renames masivos | Alta | Alto | Canary file + compilar módulo por módulo |
| BigOperators/Finset incompatible | Media | Alto | Subfase 4 es la más larga por esto |
| WF recursion opacity rompe proofs | Media | Alto | `@[semireducible]` o refactor; de-risk Goldilocks primero |
| `show` tactic cambió semántica | Media | Medio | Auditar todos los `show` en proofs |
| HashMap/HashSet migration falla | Media | Alto | Inventario pre-Subfase 3 + firewall _aux |
| **AlgebraicSemantics.lean intractable** | Media | **Muy alto** | Dedicar tratamiento especial, `simp only`, elevar heartbeats |
| **maxHeartbeats insuficiente post-migración** | Media | Alto | Preparar `simp only` para proofs >3.2M heartbeats |
| 12 sorry Poseidon aumentan | Baja | Medio | Mantener, no intentar reducir en esta fase |
| Performance regression | Baja | Medio | Benchmark antes/después |
| **S8d adaptación tipos muy compleja** | Media | Alto | Decidir A vs B después de S8a-S8c |
| **Abort: migración se vuelve inviable** | Baja | Muy alto | Tags de checkpoint + escape hatch a 4.20 |

---

## Decisiones tomadas

| # | Decisión | Alternativa descartada | Razón |
|---|----------|----------------------|-------|
| D1 | Salto directo 4.16→4.26 | Saltos intermedios (4.18→4.20→...) | Mathlib pin por versión; intermedios duplican trabajo |
| D2 | Fix módulo por módulo en orden topológico | Fix por tipo de error | Orden topológico respeta dependencias |
| D3 | Port e-graph DESPUÉS de migración | Port simultáneo | Necesita base estable primero |
| D4 | **Mantener lakefile.lean durante migración** | Convertir a TOML inmediatamente | Script phase0-test tiene IO imperativo; TOML en S7 (QA-C3) |
| D5 | Branch protegido, main intocable | Migración in-place | Prioridad: no romper nada |
| D6 | Canary file para de-risk imports | Probar imports ad-hoc | QA-R1: detección temprana de paths rotos |
| D7 | AlgebraicSemantics.lean como tarea dedicada | Agrupar con resto de Verification | QA-C6: concentra 914 simp + 14 maxHeartbeats |
| D8 | Subfase 8 en 5 etapas (a-e) | Subfase monolítica | QA-Q6: tipo adaptation es la parte difícil, separar |
| D12 | Port maximiza archivos sin deps VR1CS primero | Port lineal S8a→S8b→S8c | 10/17 archivos portables sin adaptación de tipos |
| D13 | S8c bloqueada, fusionada con S8d | S8c como etapa independiente | SemanticSpec y TV dependen de VR1CS.Basic y Rules.SoundRule |
| D14 | **Opción C: bridge adapter** (0 thms modificados) | A (typeclass, 121+ thms) / B (re-probar) | Suficiente: motor operacional completo. SemanticSpec diferida, can add via B incrementalmente |

---

## Árbol de progreso

```
Fase 9: Migración Lean 4.26 (amo-lean v2.0.0)
├── Subfase 1: Infraestructura ..................... [x] COMPLETADA 2026-02-16
│   ├── 1.1 Branch feature/lean-4.26-upgrade ...... [x]
│   ├── 1.2 lean-toolchain → v4.26.0 ............. [x]
│   ├── 1.3 lakefile.lean: Mathlib → v4.26.0 ..... [x]
│   ├── 1.4 lake update ........................... [x] Mathlib v4.26 + cache OK
│   ├── 1.5 Canary file (imports críticos) ........ [x]
│   ├── 1.6 Primer lake build (diagnóstico) ....... [x] ~74 errores en 8 archivos
│   └── 1.7 Clasificar errores .................... [x] 8 categorías identificadas
├── Subfase 2: Capa Fundacional ................... [x] COMPLETADA 2026-02-17
│   ├── DE-RISK: strongRecOn, Batteries.UInt ...... [x] No requerido (compilaron directamente)
│   ├── 2.1 Basic.lean ............................ [x] Sin cambios necesarios
│   ├── 2.2 Field/Goldilocks.lean ................. [x] val.isLt→toNat_lt_size, toNat_ofNat→toNat_ofNat', noncomputable Field
│   ├── 2.3 Field/BabyBear.lean ................... [x] Mismo patrón que Goldilocks (UInt32)
│   ├── 2.4 NTT/Field.lean ....................... [x] Sin cambios necesarios
│   ├── 2.5 Vector/Basic.lean ..................... [x] Sin cambios necesarios
│   └── 2.6 Matrix/Basic.lean ..................... [x] Sin cambios necesarios
├── Subfase 3: Motor E-Graph ...................... [x] COMPLETADA 2026-02-17
│   ├── 3.1 Inventario HashMap/HashSet API ........ [x] empty→{}, insert vía pipe
│   ├── 3.2 EGraph/Basic.lean (HashMap!) .......... [x] HashMap/HashSet empty→{}, #eval→#eval!
│   ├── 3.3 EGraph/EMatch.lean .................... [x] HashMap.empty→{}
│   ├── 3.4 EGraph/Saturate.lean .................. [x] Sin cambios necesarios
│   ├── 3.5 EGraph/Optimize.lean .................. [x] Sin cambios necesarios
│   ├── 3.6 EGraph/VerifiedRules.lean ............. [x] Sin cambios necesarios
│   ├── 3.7 EGraph/VecExpr.lean ................... [x] HashMap/HashSet empty→{}, insert vía pipe
│   └── 3.8 EGraph/Vector.lean .................... [x] HashMap/HashSet empty→{}, insert vía pipe
├── Subfase 4: Pipeline NTT ....................... [x] COMPLETADA 2026-02-17
│   ├── 4.1 NTT/RootsOfUnity.lean ................ [x] Sin cambios necesarios
│   ├── 4.2 NTT/Properties.lean ................... [x] Finset.mem_univ→Finset.mem_coe.mpr(Finset.mem_univ)
│   ├── 4.3 NTT/Bounds.lean ...................... [x] val.isLt→toNat_lt_size
│   ├── 4.4 NTT/CooleyTukey.lean ................. [x] Option.map_some'→Option.map_some
│   ├── 4.5 NTT/Correctness.lean ................. [x] map_some', mem_cons_self args, length_pos_iff
│   ├── 4.6 NTT/Spec.lean ........................ [x] length_pos_iff, map_none/some, getElem?_map args
│   ├── 4.7 NTT/ListFinsetBridge.lean ............. [x] ∑ in→∑ ∈, mem_cons_self args
│   ├── 4.8 NTT/Phase3Proof.lean .................. [x] ∑ in→∑ ∈, nodup_range, odd_iff, sum_neg_distrib
│   ├── 4.9 NTT/Radix4/*.lean .................... [x] Option.map_some'→Option.map_some
│   ├── 4.10 NTT/OrthogonalityProof.lean ......... [x] BigOperators import, Finset.mem_coe.mpr
│   └── 4.11 NTT/*.lean restantes ................ [x] BigOperators imports
│   TAG: v2.0.0-alpha2-ntt
├── Subfase 5: FRI + Protocolos ................... [x] COMPLETADA 2026-02-17
│   ├── 5.A FRI/Merkle.lean ...................... [x] mkArray→replicate, get!→[]!, size_replicate
│   ├── 5.B FRI/Prover.lean ...................... [x] get!→[]!, enum→zipIdx (tuple swap)
│   ├── 5.C FRI/Verifier.lean .................... [x] get!→[]!
│   ├── 5.D FRI/Protocol.lean .................... [x] enum→zipIdx (tuple swap)
│   ├── 5.E FRI/Proof.lean ....................... [x] get?→[]?
│   ├── 5.F FRI/*.lean restantes ................. [x] Sin cambios necesarios
│   └── 5.G Protocols/Poseidon/*.lean ............. [x] mkArray→replicate, get!→[]!, zipWith arg order, #eval→#eval!
├── Subfase 6: Integración ........................ [x] COMPLETADA 2026-02-17
│   ├── 6.A Sigma/*.lean .......................... [x] bind→flatMap, get?→[]?, String.mk warnings only
│   ├── 6.B Backends/*.lean ....................... [x] Sin cambios necesarios
│   ├── 6.C AlgebraicSemantics.lean ............... [x] mkArray→replicate, size_mkArray→size_replicate
│   │   └── NOTA: .enum conservado (deprecated pero funcional, tuple order reversal haría
│   │         impacto masivo en ~50 proofs con enumFrom)
│   └── 6.D Verification/*.lean restantes ........ [x] get!→[]!, mkArray→replicate, zipWith arg order
│   GATE: lake build COMPLETO ✓ (3119 jobs, 0 errores)
├── Subfase 7: Tests + Validación + Cleanup ....... [x] COMPLETADA 2026-02-17
│   ├── 7.1 Migrar Tests/ ........................ [x] 26 archivos, zipWith arg order fix en Oracle
│   ├── 7.2 Migrar Benchmarks/ ................... [x] 9 archivos compilan
│   ├── 7.3 Suite completa ........................ [x] 203 #eval, ALL TESTS PASSED, NTT roundtrip OK
│   ├── 7.4 Métricas baseline .................... [x] axioms=9, sorry=12, LOC=38573, 0 errores
│   ├── 7.5 Tests C/Rust ......................... [x] safety-checks 13/13 PASS, codegen OK
│   ├── 7.6 lakefile.lean → lakefile.toml ........ [-] DIFERIDO (script block requiere .lean, decisión D4)
│   ├── 7.7 Documentación ........................ [x] CLAUDE.md actualizado (toolchain v4.26.0)
│   ├── 7.8 Cleanup deprecated ................... [x] 0 deprecation warnings (String.mk, Option, Int)
│   └── 7.9 Tag v2.0.0-rc1 ...................... [ ] Pendiente (requiere commit)
│   TAG: v2.0.0-rc1
└── Subfase 8: Port E-Graph verificado ............ [x] COMPLETADA 2026-02-17
    ├── S8a: Port implementación ................... [x] COMPLETADA
    │   ├── 8.1 UnionFind verificado (1,235 LOC) .. [x] namespace VR1CS→AmoLean.EGraph.Verified
    │   └── 8.2 Core structs (252 LOC) ........... [x] CircuitNodeOp preservado (adaptar en S8d)
    ├── S8b: Port invariantes ...................... [x] COMPLETADA
    │   └── 8.3 CoreSpec (1,368 LOC, 78 thms) .... [x] zero sorry, compila limpio
    ├── S8a+: Port operacional (bonus) ............. [x] COMPLETADA
    │   ├── 8.A EMatch (201 LOC) .................. [x] import redirigido a Verified.Core
    │   ├── 8.B Saturate (70 LOC) ................. [x] sin deps externas
    │   ├── 8.C ILP (185 LOC) .................... [x] CostModel import eliminado (no se usaba)
    │   ├── 8.D ILPEncode (233 LOC) .............. [x] namespace adaptado
    │   ├── 8.E ILPSolver (314 LOC) .............. [x] namespace adaptado
    │   ├── 8.F ParallelMatch (209 LOC) .......... [x] namespace adaptado
    │   └── 8.G ParallelSaturate (125 LOC) ....... [x] namespace adaptado
    │   TOTAL: 10 archivos, 4,192 LOC, 121 teoremas, zero sorry
    │   BUILD: 3129 jobs, 0 errores
    ├── S8c: Port soundness ........................ [-] DIFERIDA (Opción C)
    │   ├── 8.4 SemanticSpec ...................... [-] no necesaria para motor operacional
    │   └── 8.5 TranslationValidation ............ [-] diferida, puede hacerse incrementalmente
    ├── S8d: Bridge Adapter (OPCIÓN C) ............. [x] COMPLETADA
    │   ├── 8.6 Bridge.lean (132 LOC) ............ [x] Expr Int ↔ CircuitNodeOp EGraph
    │   │   ├── addExpr: Expr Int → EGraph
    │   │   ├── extract: EGraph → Expr Int
    │   │   ├── exprPatternToCircuit: pattern bridge
    │   │   ├── mkRule: convenience wrapper
    │   │   └── optimize: pipeline end-to-end
    │   ├── 8.7 Test integración ................. [x] 8 tests, all passing
    │   │   ├── embedding + sharing ✓
    │   │   ├── power decomposition ✓
    │   │   ├── e-matching via bridge ✓
    │   │   ├── saturation + fixpoint ✓
    │   │   └── extraction + cost model ✓
    │   └── DECISIÓN D14: Opción C (bridge, 0 teoremas modificados)
    │       vs A (typeclass, ~2x esfuerzo) vs B (re-probar, ~121+ thms)
    │   TOTAL: 11 archivos, 4,324 LOC, 121 teoremas, zero sorry
    │   BUILD: 3130 jobs, 0 errores
    ├── S8e: Consumidores downstream ............... [x] COMPLETADA
    │   ├── 8.9 Rules.lean (144 LOC) .............. [x] 10 verified rules → Bridge
    │   │   ├── 6 identity (addZero, mulOne, mulZero)
    │   │   ├── 2 factorization (factorLeft, factorRight)
    │   │   └── 2 distributivity (distribLeft, distribRight)
    │   ├── 8.10 Optimize.lean (126 LOC) ......... [x] verified pipeline end-to-end
    │   │   └── 9/9 benchmarks: 100% reduction, 19→0 ops
    │   ├── 8.11 VerifiedRules.lean fix .......... [x] List.append_eq_nil → _iff (4.26 API)
    │   └── 8.12 VecExpr, Vector ................. [-] ya compatibles (EClassId=Nat)
    │   TOTAL: 13 archivos, 4,594 LOC, 121 teoremas, zero sorry
    │   BUILD: 3134 jobs, 0 errores
    └── S8f: Limpieza ............................. [x] COMPLETADA
        ├── 8.13 Deprecar EGraph unverified ....... [x] DEPRECATED notices en Basic/EMatch/Saturate/Optimize
        └── 8.14 Cost model refinement ........... [x] ENode.simplicity + isBetter tiebreaker
        │   ├── computeCosts: isBetter replaces strict < ...... [x]
        │   ├── updateBest: isBetter replaces strict < ........ [x]
        │   ├── union: unchanged (CoreSpec 78 thms intact) .... [x]
        │   └── Test: ((x+0)*1)+(y*0) → x (was x+0) ......... [x] ✓
    TAG: v2.1.0
```

---

## Diagnóstico primer build (2026-02-16)

### Módulos que fallan (18 targets)

```
AmoLean.Field.Goldilocks          — 23 errores
AmoLean.Field.BabyBear            — 14 errores
AmoLean.EGraph.Basic              — 11 errores
AmoLean.Protocols.Poseidon.Spec   — 11 errores
AmoLean.Verification.FRI_Properties — 6 errores
AmoLean.Sigma.Expand              — 7 errores
AmoLean.FRI.Merkle                — 2 errores
AmoLean.Correctness               — 1 error
+ cascadas por bad import de Mathlib.Algebra.BigOperators.Ring
```

### Clasificación de errores por categoría

| Categoría | Cantidad | Archivos | Fix |
|-----------|----------|----------|-----|
| **`UInt64.val` / `UInt32.val` no existe** | ~15 | Goldilocks, BabyBear | `.toNat` o nueva API UInt |
| **`Array.get!` no existe** | ~10 | Poseidon/Spec, FRI_Properties, Merkle | `.get!` → `a[i]!` o `Array.getD` |
| **`Array.mkArray` no existe** | 1 | Poseidon/Spec | `Array.mkArray` → `Array.replicate` o similar |
| **`Std.HashMap.empty` no existe** | 2 | EGraph/Basic | `{}` o `.emptyWithCapacity` |
| **`Std.HashSet.empty` no existe** | 3 | EGraph/Basic | `{}` o reemplazar con Array |
| **`Std.HashSet.empty.insert` no existe** | 2 | EGraph/Basic | Constructor directo |
| **`List.bind` no existe** | 2 | Sigma/Expand | `.flatMap` o `List.flatMap` |
| **`List.get?` no existe** | 2 | Sigma/Expand | `.get?` → `a[i]?` |
| **`Nat.and_pow_two_sub_one_eq_mod` no existe** | 2 | Goldilocks | Buscar nuevo nombre en Mathlib |
| **`Mathlib.Algebra.BigOperators.Ring` bad import** | 7+ cascada | NTT/*.lean | Path renombrado en Mathlib |
| **`sorry` abort eval** | ~9 | EGraph, Poseidon | v4.26 no evalúa con sorry — workaround `#eval` |
| **Type mismatch / unsolved goals** | ~10 | Goldilocks, BabyBear | Proofs rotas por cambio UInt API |
| **Compiler IR check failed** | 2 | Goldilocks, BabyBear | `instFieldXField._lam_3` — tobj vs scalar |

### Veredicto

**~74 errores totales** en ~8 archivos (excluyendo cascadas de import).
**Clasificación**: Mayormente mecánicos (API renames). NO hay >300 errores no triviales → **NO activar escape hatch**.

**Categorías principales**:
1. **UInt API** (~15): `.val` → nuevo accessor (probablemente `.toNat`)
2. **Array API** (~13): `.get!` → `[i]!`, `.mkArray` → nuevo nombre
3. **HashMap/HashSet** (~7): API eliminada → nueva API
4. **Mathlib import** (1 + cascada): `BigOperators.Ring` → nuevo path
5. **Proofs rotas** (~12): Consecuencia de cambio UInt API
6. **Sorry eval abort** (~9): v4.26 previene eval con sorry — no es error real de lógica
7. **List API** (~4): `.bind` → `.flatMap`, `.get?` → indexación
8. **Compiler IR** (2): Bug de codegen Field instance — investigar

### Próximos pasos

1. **S8c (DIFERIDA)** — SemanticSpec/TranslationValidation si se necesitan proofs end-to-end
2. **Merge a main** — Tras validación final, `git merge feature/lean-4.26-upgrade`
3. **Nuevas funcionalidades** — Explorar nuevas reglas de optimización sobre el motor verificado

---

---

## Resumen de migración Subfases 2-6 (2026-02-17)

### Resultado: `lake build` COMPLETO — 3134 jobs, 0 errores (con Verified E-Graph: 13 archivos, 4,594 LOC, 121 teoremas)

### API mapping Lean 4.16 → 4.26 (descubierto durante migración)

| Old (4.16) | New (4.26) | Archivos afectados |
|---|---|---|
| `x.val.isLt` | `UInt64.toNat_lt_size x` / `UInt32.toNat_lt_size x` | Goldilocks, BabyBear, Bounds |
| `UInt64.toNat_ofNat` (simp) | `UInt64.toNat_ofNat'` | Goldilocks |
| `UInt32.toNat_ofNat` (simp) | `UInt32.toNat_ofNat'` | BabyBear |
| `Nat.and_pow_two_sub_one_eq_mod` | `Nat.and_two_pow_sub_one_eq_mod` | Goldilocks |
| `instance : Field X` | `noncomputable instance : Field X` | Goldilocks, BabyBear |
| `Array.mkArray n v` | `Array.replicate n v` | 6 files |
| `Array.size_mkArray` | `Array.size_replicate` (implicit) | AlgebraicSemantics, Merkle |
| `a.get! N` | `a[N]!` | 6 files |
| `List.bind` | `List.flatMap` | Sigma/Expand |
| `l.get? i` | `l[i]?` | Sigma/Expand, FRI/Proof |
| `Std.HashMap.empty` | `{}` | EGraph/Basic, EMatch, VecExpr, Vector |
| `Std.HashSet.empty` | `{}` | EGraph/Basic, VecExpr, Vector |
| `a.zipWith b f` | `a.zipWith f b` | Poseidon/Spec, Poseidon_Semantics |
| `List.enum` | `List.zipIdx` (tuple `(Nat×α)→(α×Nat)`) | Prover, Protocol, Integration |
| `#eval` (sorry-dependent) | `#eval!` | EGraph/Basic, Poseidon |
| `Mathlib.Algebra.BigOperators.Ring` | `...Ring.Finset` | 4 NTT files |
| `Option.map_none'` | `Option.map_none` | Spec, CooleyTukey |
| `Option.map_some'` | `Option.map_some` | Spec, CooleyTukey, Correctness, Radix4 |
| `List.length_pos.mpr` | `List.length_pos_iff.mpr` | Spec, Correctness |
| `List.mem_cons_self x xs` | `List.mem_cons_self` (implicit) | Correctness, ListFinsetBridge |
| `List.getElem?_map f l i` | `List.getElem?_map` (implicit) | Spec |
| `List.length_map l f` | `List.length_map f` (l implicit) | Spec |
| `List.length_zipWith f a b` | `List.length_zipWith` (implicit) | Spec |
| `Finset.mem_univ _` (coerced) | `Finset.mem_coe.mpr (Finset.mem_univ _)` | OrthogonalityProof, Properties |
| `List.nodup_range _` | `List.nodup_range` (implicit) | Phase3Proof |
| `∑ i in Finset.range n, f i` | `∑ i ∈ Finset.range n, f i` | Phase3Proof, ListFinsetBridge |
| `Nat.odd_iff_not_even.mpr` | `Nat.not_even_iff_odd.mp` | Phase3Proof |
| `Finset.sum_neg_distrib.symm` | `← Finset.sum_neg_distrib` | Phase3Proof |
| `List.append_eq_nil` | `List.append_eq_nil_iff` | EGraph/VerifiedRules |

### Decisiones tomadas durante la migración

| # | Decisión | Razón |
|---|----------|-------|
| D9 | `.enum` conservado en AlgebraicSemantics (deprecated, funcional) | Tuple order reversal `(Nat×α)→(α×Nat)` impactaría ~50 proofs con `enumFrom` |
| D10 | `.enum` migrado a `.zipIdx` solo en código sin proofs | FRI/Prover, Protocol, Integration — solo tuple swap necesario |
| D11 | `UInt64.toNat_ofNat'` como bridge lemma clave | Resuelve mismatch `UInt64.ofNat` vs `OfNat.ofNat` en simp chains |

### Warnings residuales (no errores)

- `Option.none_orElse` → `Option.or_none` (deprecated, Correctness.lean)
- `String.mk` → `String.ofList` (deprecated, Sigma/Basic.lean, 6 occurrences)
- `simp_wf` does nothing (FRI_Properties.lean)
- 12 `sorry` warnings (Poseidon_Semantics.lean — pre-existentes, no nuevos)
- ~150 unused variable / unused section variable warnings (pre-existentes)

*Última actualización: 2026-02-17 (S8f completada — Fase 9 COMPLETA)*
*Autor: Claude Opus 4.6 + Manuel Puebla*
*QA: 1 ciclo completado — 3 blockers resueltos, 8 concerns integrados*
*Verified E-Graph: 13 archivos portados, 4,594 LOC, 121 teoremas, zero sorry*
