# Insights: Verified Code Generation Integration — AMO-Lean + TrustLean v3.0

**Fecha**: 2026-03-29
**Dominio**: lean4
**Estado del objeto**: upgrade (proyecto existente con brecha crítica identificada)

## 1. Análisis del Problema

### El problema central

AMO-Lean tiene **7 archivos de codegen (~3,515 LOC)** que emiten C/Rust via string interpolation sin verificación:

| Archivo AMO-Lean | LOC | Target | Funciones `partial def` | Verificación |
|-------------------|-----|--------|------------------------|--------------|
| `AmoLean/CodeGen.lean` | 195 | C | `lowLevelToC` | CERO |
| `AmoLean/Backends/Rust.lean` | 565 | Rust | `exprToRust` + 17 helpers | CERO |
| `AmoLean/FRI/CodeGen.lean` | 755 | C | `cryptoSigmaToC` + 21 helpers | CERO (bug AVX2 documentado) |
| `AmoLean/Sigma/CodeGen.lean` | 274 | C | `exprToC` + 13 helpers | CERO |
| `AmoLean/Vector/CodeGen.lean` | 417 | C (SIMD) | `vecExprToC` + 13 helpers | CERO |
| `Protocols/Poseidon/CodeGen.lean` | 1,124 | C | Poseidon hash emission | CERO |
| `Protocols/Poseidon/Constants/CodeGen.lean` | 185 | C | Constant tables | CERO |
| **Total** | **3,515** | | **78+ partial def** | **CERO** |

**Incidente**: 11/12 archivos Rust + 9 archivos C defectuosos compartidos con colegas. Bugs: truncación u32/u64, overflow, syntax errors, wrong field widths. Todos en la capa de string emission, no en las pruebas formales.

### Lo que TrustLean v3.0 ofrece (ya es dependencia Lake)

| Capacidad TrustLean | Teorema clave | LOC | Relevancia |
|---------------------|---------------|-----|------------|
| Core IR (12 constructores Stmt) | `evalStmt_fuel_mono` | 1,136 | Semántica formal para C |
| 3 Frontends verificados | `ArithExpr/BoolExpr/ImpStmt.compile_correct` | 1,070 | Modelo de cómo implementar `CodeGenSound` |
| Bridge AMO-Lean → Stmt | `expandedSigmaToStmt_correct_full` | 1,659 | **Ya wired parcialmente** |
| MicroC roundtrip | `parseMicroC_roundtrip_full` | 2,807 | Garantía de string canónico |
| Int64 wrapping (v3.0) | `binOp_agreement` | 768 | Resuelve bug truncación |
| Call semantics (v3.0) | `evalMicroC_withCalls_fuel_mono` | 994 | Funciones no-recursivas |
| C Backend | `stmtToC` + 34 property theorems | 763 | Braces balanceados, sanitización |
| Rust Backend | `stmtToRust` | ~200 | Pretty-printer (fuera TCB) |
| Typeclass system | `Pipeline.sound` | 126 | Composición automática |
| **Total** | **623 propiedades verificadas** | **17,233** | **0 sorry, 0 axiomas** |

### Gap: lo que AMO-Lean usa vs. lo disponible

| Capacidad | Disponible en TrustLean | AMO-Lean la usa? | Gap |
|-----------|------------------------|-------------------|-----|
| `expandedSigmaToStmt` (Bridge) | ✓ probado | Parcial (Bridge/TrustLean.lean) | Wiring incompleto |
| `stmtToMicroC` + roundtrip | ✓ probado | **NO** — usa string emission directa | **CRÍTICO** |
| `evalMicroC_int64` | ✓ probado (v3.0) | **NO** | **CRÍTICO** |
| `CodeGenSound` typeclass | ✓ definido | **NO** — ningún DSL AMO lo implementa | **CRÍTICO** |
| `Pipeline.sound` | ✓ probado | **NO** — no hay instancia AMO | **CRÍTICO** |
| `sanitizeIdentifier` | ✓ probado | **NO** — backends hacen su propia | Gap menor |
| C backend properties (34 thms) | ✓ probado | **NO** — usa emitters propios | Gap |
| MicroC `parseMicroC_roundtrip_full` | ✓ probado | **NO** — disponible pero no invocado | Gap |

## 2. Lecciones Aplicables

### Lecciones reutilizables

| ID | Título | Aplicabilidad |
|----|--------|---------------|
| **L-310** | End-to-End Pipeline via Generic Typeclasses | DIRECTA — describe la arquitectura TrustLean. O(n+m) scaling con CodeGenerable + CodeGenSound + BackendEmitter |
| **L-297/L-311** | Three-Part Codegen Contract | FUNDACIONAL — (1) fuel, (2) result semantics, (3) frame preservation. Este es el contrato que cada frontend debe probar |
| **L-572/L-512** | Three-Tier Bridge Pattern | CRÍTICA — Shell (partial/IO) → Core (total/verified) → Bridge (composition). Translation Validation cierra gaps |
| **L-513** | Compositional End-to-End Proofs | REUTILIZABLE — cada stage preserva invariante, componer via transitividad. ~30 líneas para proof end-to-end |
| **L-617** | #eval Tests as Specification Oracle | PRÁCTICA — 10+ tests cubriendo constructores como high-confidence substitute cuando formal proofs son costosos |
| **L-348** | Aggressive Parenthesization | STANDARD — envolver TODAS operaciones binarias en paréntesis para C. Elimina bugs de precedencia |
| **L-308** | Backend Emitter Architecture | DIRECTA — emitters como pretty-printers fuera del TCB. Tres métodos: emitStmt, emitFunction, emitHeader |
| **L-338** | Fuel Composition via Max | CRÍTICA — componer fuel con `max`, NOT `+`. Mantiene bounds pequeños para inducción |

### Anti-patrones a evitar

| Anti-patrón | Descripción | Lección |
|-------------|-------------|---------|
| **String emission sin roundtrip** | Emitir C/Rust como strings sin probar `parse(print(x)) = x` | L-614 |
| **Silent defaults en field dispatch** | `match p with ... | _ => (31, 1, 0, 32)` → 5 archivos con parámetros incorrectos | feedback_codegen_emission_gap |
| **Type width mismatch** | Emitter usa `u32` para acumulador que necesita `u64` | feedback_codegen_emission_gap |
| **Raw operators en vez de field ops** | Emitir `+` en vez de `field_add` → reducción modular omitida | feedback_codegen_emission_gap |
| **Identity passes como completeness** | `fun x => x` donde debería haber reducción → stubs no documentados | L-436 |
| **Defer fundacionales** | Insertar fases fáciles para postergar nodos FUND/CRIT | feedback_no_scope_creep |
| **Opaque Nat.repr** | `Nat.repr`/`toString` son opacos al kernel → roundtrip imposible. Usar `natToChars` custom | L-612 |

## 3. Bibliografía Existente Relevante

### Papers clave (ordenados por prioridad)

| # | Paper | Carpeta | Relevancia directa |
|---|-------|---------|---------------------|
| 1 | **CryptOpt**: Verified Compilation with Randomized Search (Kuepper 2023) | verificacion | Pipeline verificado para crypto: e-graphs + SMT + equivalence checking. **Modelo directo** |
| 2 | **Accelerating Verified-Compiler Development** (Gross 2022) | verificacion | Framework Coq para compiladores verificados desde reglas de rewrite. Patrón Fiat-Crypto |
| 3 | **Verified Compiler for Functional Tensor Language** (Liu PLDI 2024) | verificacion | Compilador verificado Coq para tensores. Decouple compute/storage. Soundness-preserving types |
| 4 | **HEC**: Equivalence Verification via Equality Saturation | verificacion | E-graphs + MLIR para verificar transformaciones source-to-source |
| 5 | **Lean-egg**: Equality Saturation Tactic for Lean (Rossel POPL 2026) | zk-circuitos | Táctica Lean 4 con e-graphs. Integración directa posible |
| 6 | **ROVER**: RTL Optimization via Verified E-Graph Rewriting | zk-circuitos | Certificados de verificación para rewriting de hardware |
| 7 | **HELIX**: Verified Translation Functional→Imperative (Zaliva 2018) | verificacion | Coq verified operator language. Patrón: specs funcionales → código imperativo verificado |
| 8 | **Bidirectional Grammars** (Morrisett JAR 2017) | verificacion | DSL bidireccional para decode/encode con roundtrip en Coq |
| 9 | **Formally Verified NTT** (Trieu) | verificacion/ntt | Especificación formal de NTT en Rocq para derivar implementaciones verificadas |
| 10 | **egg: Fast and Extensible Equality Saturation** (Willsey POPL 2021) | egraphs-treewidth | Fundación de e-graphs modernos. Rebuilding + e-class analyses |

### Gaps bibliográficos identificados

1. **TCB formalization** — No hay papers sobre minimización formal del TCB para compiladores
2. **Roundtrip verification architectures** — Solo Bidirectional Grammars (Morrisett) cubre esto
3. **Proof-Carrying Code moderno** — Implícito en CompCert/Fiat-Crypto pero no formalizado como framework
4. **Cost model verification** — Modelos de costo usados pero raramente verificados formalmente
5. **Certified modular optimization passes** — Composición de passes verificados es gap abierto

## 4. Estrategias y Decisiones Previas

### Estrategias ganadoras (de proyectos previos)

| Estrategia | Resultado | Aplicabilidad |
|------------|-----------|---------------|
| **Path A: Verified C via Trust-Lean** | 0 defectos en 1,659 LOC, 26 theorems, 0 sorry | DIRECTA — usar VerifiedCodeGen → TrustLean → MicroC → C |
| **Isomorphism Layer FIRST** | Cero bugs de VarName (injectivity probada antes de implementar) | FUNDACIONAL — probar `scalarVar_to_varName_injective` antes de lowering |
| **Modular Bridge Predicates** | `scalarBridge + loopBridge + memBridge` independientes | COMPOSICIONAL — preservación modular por disjuntividad |
| **Fuel composition via Max** | Fuel se compone maximizando, no sumando | CRÍTICA para inducción de loops |
| **Type-First Isomorphism** | Define injection FIRST, prove bridge SECOND | Previene bugs de conversión de tipos |

### Errores evitados (incidentes documentados)

| Error | Causa raíz | Costo | Prevención |
|-------|-----------|-------|------------|
| 11/12 Rust defectuosos | String emission sin verificación (Path B) | Reputación dañada | NUNCA Path B para código externo |
| 5 archivos con parámetros incorrectos | Silent default `(31, 1, 0, 32)` en dispatch | 5 archivos rehechos | PANIC en unknown; no defaults |
| 4 bugs de overflow | `u32` donde necesitaba `u64` | Debugging extenso | Query bounds ANTES de emitir |
| Two-layer gap (Fase 24) | Rules sin executor → saturación inoperante | 500+ LOC mitigación | Definir saturation loop junto con rules |
| Phase 22 disaster | 7 nodos "completos" sin wiring_check | Reescritura de 3 archivos | SIEMPRE wiring_check antes de declarar completo |

### Política establecida (de memory)

> **NUNCA usar Path B (string emission) para código externo.** Solo Path A (VerifiedCodeGen → TrustLean → MicroC → C). Si se necesita Rust: usar `extern "C"` FFI para llamar kernel C verificado.

## 5. Mapa de Integración: Archivos AMO-Lean ↔ TrustLean

### Qué existe y cómo se conecta

```
AMO-LEAN (actual)                          TRUST-LEAN v3.0 (disponible)
═══════════════                            ═══════════════════════════

E-Graph Verified Engine ──────────────┐
  (147 theorems, 0 sorry)            │
  AmoLean/EGraph/Verified/*          │
                                      │
  ↓ extraction                        │
                                      │
MixedExpr / ExpandedSigma            │    Typeclass/CodeGenerable.lean
  AmoLean/Bridge/TrustLean.lean ─────┼──→ Typeclass/CodeGenSound.lean
  (30 roundtrip theorems)            │    Pipeline.lean (Pipeline.sound)
  (PARCIAL: solo ScalarVar, IdxExpr) │
                                      │
  ↓ GAP: MixedExpr→ExpandedSigma     │    Bridge/Types.lean (ExpandedSigma)
         no está implementado         │    Bridge/Compile.lean (expandedSigmaToStmt)
                                      │    Bridge/Correctness.lean (correct_full)
                                      │
  ↓ GAP: no pasa por aquí ────────────┤    Core/Stmt.lean (12 constructores)
                                      │    Core/Eval.lean (evalStmt)
                                      │    Core/FuelMono.lean (fuel_mono GATE)
                                      │
  ↓ GAP: no pasa por aquí ────────────┤    MicroC/AST.lean (11 stmt + 7 expr)
                                      │    MicroC/Simulation.lean (stmtToMicroC_correct)
                                      │    MicroC/PrettyPrint.lean (microCToString)
                                      │    MicroC/RoundtripMaster.lean (roundtrip_full)
                                      │    MicroC/Int64.lean (wrapInt64) ← v3.0
                                      │    MicroC/CallTypes.lean (calls) ← v3.0
                                      │
  ↓ BYPASS (string emission) ─────×───┘    Backend/CBackend.lean (stmtToC, 34 thms)
                                           Backend/RustBackend.lean (stmtToRust)
PATH B (actual, roto):
  AmoLean/CodeGen.lean ───→ s!"..." ──→ String C (sin verificar)
  AmoLean/Backends/Rust.lean → s!"..." → String Rust (sin verificar)
  AmoLean/FRI/CodeGen.lean ──→ s!"..." → String C (bug AVX2)
  AmoLean/Sigma/CodeGen.lean → s!"..." → String C (sin verificar)
  AmoLean/Vector/CodeGen.lean → s!"..." → String C SIMD (sin verificar)
```

### El path correcto (cómo debería fluir)

```
MixedExpr (post-extraction del e-graph)
    ↓ [NUEVO] convertMixedExprToExpandedSigma (probar inyectividad)
ExpandedSigma
    ↓ [EXISTENTE] expandedSigmaToStmt (TrustLean Bridge, probado)
Trust-Lean Stmt
    ↓ [EXISTENTE] stmtToMicroC (probado: stmtToMicroC_correct)
MicroCStmt
    ↓ [EXISTENTE] microCToString (probado: parseMicroC_roundtrip_full)
String C canónico
    ↓ [EXISTENTE] Backend/CBackend.lean (34 property theorems)
    ↓   O
    ↓ [EXISTENTE] Backend/RustBackend.lean (pretty-printer)
Código C / Rust
```

### Archivos a crear / modificar

| Archivo | Acción | LOC estimado | Dependencias |
|---------|--------|-------------|--------------|
| `AmoLean/Bridge/MixedExprToExpandedSigma.lean` | **CREAR** | ~300 | Bridge/TrustLean.lean, EGraph/Verified/* |
| `AmoLean/Bridge/MixedExprCodeGenSound.lean` | **CREAR** | ~400 | MixedExprToExpandedSigma, TrustLean/Typeclass/* |
| `AmoLean/Bridge/FieldInt64Bridge.lean` | **CREAR** | ~250 | TrustLean/MicroC/Int64*.lean |
| `AmoLean/Bridge/TrustLean.lean` | **MODIFICAR** | +100 | Extender roundtrips para MixedExpr |
| `AmoLean/Bridge/MicroC/BabyBear.lean` | **MODIFICAR** | +50 | Agregar Int64 agreement |
| `AmoLean/Bridge/MicroC/Goldilocks.lean` | **CREAR** | ~200 | MicroC/Int64, field_goldilocks |
| `Tests/Integration/VerifiedCodeGenE2E.lean` | **CREAR** | ~150 | Roundtrip tests compilables |
| **Total nuevo** | | **~1,450** | |

### Archivos a deprecar (Path B → marcados como UNTRUSTED)

| Archivo | Acción | Nota |
|---------|--------|------|
| `AmoLean/CodeGen.lean` | Marcar `UNTRUSTED — internal prototyping only` | No eliminar, marcar |
| `AmoLean/Backends/Rust.lean` | Marcar `UNTRUSTED` | Reemplazado por TrustLean RustBackend |
| `AmoLean/FRI/CodeGen.lean` | Marcar `UNTRUSTED` + documentar bug AVX2 | El más peligroso |
| `AmoLean/Sigma/CodeGen.lean` | Marcar `UNTRUSTED` | Reemplazado por ExpandedSigma→Stmt |
| `AmoLean/Vector/CodeGen.lean` | **EXCEPCIÓN**: SIMD no tiene path TrustLean | Necesita solución separada |

## 6. Cadena de Verificación Propuesta

### Nivel 1: Conversión MixedExpr → ExpandedSigma

**Qué probar:**
```lean
theorem convertMixedExpr_injective :
    Function.Injective convertMixedExprToExpandedSigma

theorem convertMixedExpr_semantics_preserving (e : MixedExpr) (env : FieldEnv) :
    evalMixedExpr e env = evalExpandedSigma (convertMixedExprToExpandedSigma e) (convertEnv env)
```

**Patrón**: Adaptar de `Bridge/TrustLean.lean` (30 roundtrip theorems existentes para ScalarVar, IdxExpr).

**Constructores MixedExpr a cubrir** (20 total):
- Primitivos (13): addE, mulE, subE, negE, smulE, shiftLeftE, shiftRightE, bitAndE, bitXorE, bitOrE, constMaskE, constE, witnessE
- Memoria (3): pubInputE, kronPackE, kronUnpackLoE/HiE
- Reducción (3): harveyReduceE, montyReduceE, barrettReduceE
- Meta (1): reduceE (descompone en primitivos via reglas pre-computadas)

**Riesgo**: harveyReduceE/montyReduceE/barrettReduceE requieren emit de condicionales (`Stmt.ite`) y algoritmos completos (REDC, Barrett division). NO son identity passes.

### Nivel 2: ExpandedSigma → Stmt (ya probado)

**Teorema existente en TrustLean:**
```lean
theorem expandedSigmaToStmt_correct_full (sigma : ExpandedSigma)
    (env : SigmaEnv) (llEnv : LowLevelEnv)
    (hWF : wellFormed sigma)
    (hBridge : fullBridge env llEnv) :
    ∃ llEnv' fuel,
      evalStmt fuel llEnv (expandedSigmaToStmt sigma) = some (.normal, llEnv') ∧
      fullBridge (denotation env sigma) llEnv'
```

**Acción**: Solo wiring — conectar output de Nivel 1 con input de este teorema.

### Nivel 3: Stmt → MicroC → String (ya probado)

**Teoremas existentes en TrustLean:**
```lean
theorem stmtToMicroC_correct (fuel : Nat) (env : LowLevelEnv) (mcEnv : MicroCEnv)
    (stmt : Stmt) (hbridge : microCBridge env mcEnv) ... :
    evalMicroC fuel mcEnv (stmtToMicroC stmt) = some (oc, mcEnv') ∧
    microCBridge env' mcEnv'

theorem parseMicroC_roundtrip_full (s : MicroCStmt) (hs : WFStmt s) :
    parseMicroC (microCToString s) = some s
```

**Acción**: Solo wiring — conectar output de Nivel 2.

### Nivel 4: Int64 Agreement (v3.0 — resuelve truncación)

**Teorema nuevo en TrustLean v3.0:**
```lean
theorem binOp_agreement (op : MicroCBinOp) (a b : Int) :
    InInt64Range (unboundedOp a b) →
    evalMicroCBinOp_int64 op (.int a) (.int b) =
    evalMicroCBinOp op (.int a) (.int b)
```

**Aplicación**: Para cada operación de campo (BabyBear: u32, Goldilocks: u64), probar que los resultados intermedios caben en Int64Range. Esto garantiza que el evaluador con wrapping produce el mismo resultado que el unbounded.

**Archivo nuevo**: `FieldInt64Bridge.lean` — probar `InInt64Range` para cada operación de cada campo.

### Nivel 5: Composición end-to-end

**Teorema objetivo:**
```lean
theorem verified_codegen_pipeline (e : MixedExpr) (env : FieldEnv) (p : Prime) (hw : HWConfig) :
    let sigma := convertMixedExprToExpandedSigma e
    let stmt := expandedSigmaToStmt sigma
    let microc := stmtToMicroC stmt
    let cCode := microCToString microc
    -- 1. Roundtrip: el string es canónico
    parseMicroC cCode = some microc ∧
    -- 2. Semántica: evaluar el MicroC da el mismo resultado
    ∃ fuel mcEnv', evalMicroC fuel (initEnv env) microc = some (.normal, mcEnv') ∧
    -- 3. Corrección: el resultado coincide con evalMixedExpr
    extractResult mcEnv' = evalMixedExpr e env
```

## 7. Síntesis de Insights

### Hallazgos clave (Top 10)

1. **TrustLean v3.0 ya tiene TODO lo necesario** para reemplazar Path B. La cadena `ExpandedSigma → Stmt → MicroC → String` está probada end-to-end con 623 propiedades, 0 sorry, 0 axiomas. El trabajo es de **integración**, no de investigación.

2. **El gap crítico es UN archivo**: `MixedExprToExpandedSigma.lean` (~300 LOC). Este archivo convertiría MixedExpr (output del e-graph) a ExpandedSigma (input de TrustLean). Todo lo demás ya existe.

3. **Int64 wrapping (v3.0) resuelve el bug de truncación** que causó 11/12 Rust defectuosos. `binOp_agreement` prueba que si los valores intermedios caben en Int64Range, el resultado con wrapping es idéntico al unbounded.

4. **El typeclass `CodeGenSound` es el contrato formal** que previene los bugs de emission. Obliga a probar 3 cosas: (1) fuel suficiente, (2) resultado correcto, (3) variables preservadas. Sin esto, cualquier emitter puede producir basura.

5. **SIMD/AVX no tiene solución via TrustLean** — requiere path separado. FRI/CodeGen.lean AVX2 tiene bug documentado ("uses native integer mul+add, NOT modular field ops"). Este path necesita: o bien extensión de TrustLean, o tests de compilación + differential testing.

6. **Los 7 archivos Path B no deben eliminarse sino marcarse UNTRUSTED**. Pueden servir para prototyping interno, pero NUNCA para código compartido externamente.

7. **El patrón Three-Tier Bridge (L-572)** es la arquitectura correcta: Tier 1 (Shell con IO, partial def) → Tier 2 (Core verificado, total) → Tier 3 (Bridge proofs). Los emitters actuales son Tier 1 sin Tier 2/3.

8. **Non-vacuity via `native_decide`** sobre valores concretos es el approach pragmático. SimBridge.lean ya lo hace para BabyBear/Mersenne31. Extender a Goldilocks y KoalaBear.

9. **Roundtrip testing como CI gate** habría detectado los 20 archivos defectuosos en 30 segundos. `#eval INTT(NTT(x)) == x` debería ser mandatory antes de cualquier merge.

10. **CryptOpt (Kuepper PLDI 2023)** es el modelo de referencia más cercano: pipeline verificado para crypto con e-graphs + SMT + equivalence checking. Estudiar su TCB boundary.

### Riesgos identificados

| Riesgo | Probabilidad | Impacto | Mitigación |
|--------|-------------|---------|------------|
| MixedExpr → ExpandedSigma pierde semántica en constructores de reducción | Alta | Bloqueante | Probar `semantics_preserving` para CADA constructor, especialmente harveyReduceE |
| `HashMap.fold` sin principio de inducción en Lean 4 | Media | Delay 1-2 semanas | Usar patrón `processKeys` (L-200): recursión explícita sobre `toList` |
| Fields con overflow en Int64Range | Media | Bug silencioso | Probar `InInt64Range` para cada operación de cada campo. Goldilocks (u64) es tight |
| SIMD path sin solución verificada | Alta | Feature gap | Documentar como UNTRUSTED; agregar tests de compilación como mitigación |
| Regression en pruebas existentes | Baja | Delay | `lake build` completo antes y después de cada cambio |

### Recomendaciones para planificación

**Fase propuesta: "Verified Code Generation Pipeline" (~1,450 LOC nuevos)**

**Orden topológico:**

```
N.1 MixedExprToExpandedSigma (FUND, ~300 LOC)
  ↓
N.2 MixedExprCodeGenSound (CRIT, ~400 LOC)  ←  depende de N.1
  ↓
N.3 FieldInt64Bridge (CRIT, ~250 LOC)        ←  independiente, parallelizable con N.1-N.2
  ↓
N.4 GoldilocksMicroC (PAR, ~200 LOC)         ←  depende de N.3
  ↓
N.5 PipelineComposition (CRIT, ~150 LOC)     ←  depende de N.2 + N.3
  ↓
N.6 E2E Tests + Deprecation (HOJA, ~150 LOC) ←  depende de N.5
```

**Budget**: ~1,450 LOC nuevos + ~100 LOC modificaciones
**Teoremas esperados**: ~25-35
**Sorry target**: 0
**Axiomas target**: 0

### Recursos prioritarios

1. **AmoLean/Bridge/TrustLean.lean** (585 LOC) — el bridge existente; extender, no reescribir
2. **AmoLean/EGraph/Verified/Bitwise/TrustLeanBridge.lean** — patrón de referencia: `MixedNodeOp → Stmt` con `lower_correct`. Adaptar este patrón
3. **.lake/packages/TrustLean/TrustLean/MicroC/Int64Agreement.lean** — `binOp_agreement` para Int64
4. **.lake/packages/TrustLean/TrustLean/Bridge/Correctness.lean** — `expandedSigmaToStmt_correct_full` (capstone theorem)
5. **CryptOpt paper** (Kuepper PLDI 2023) — modelo de TCB boundary para crypto codegen
6. **L-297/L-311** (Three-Part Contract) — especificación formal del contrato `CodeGenSound`
7. **L-572** (Three-Tier Bridge) — arquitectura Shell → Core → Bridge
8. **feedback_codegen_emission_gap.md** — lección del incidente, rules exactas de emission

## 8. Limitaciones de TrustLean que requieren solución aparte

### SIMD/AVX

TrustLean no soporta intrinsics vectoriales. Las opciones son:
1. **Extensión de TrustLean**: Agregar `VecStmt` al Core IR (alto esfuerzo, ~2-4 semanas)
2. **Tests de compilación**: Compilar output con `gcc -Wall -Werror -mavx2` + differential testing contra scalar (pragmático)
3. **Marcar UNTRUSTED**: Documentar que SIMD output no tiene garantías formales (mínimo viable)

Recomendación: Opción 2 (tests) como mitigación inmediata, opción 1 como roadmap.

### Aritmética modular para inputs arbitrarios

TrustLean opera con `Int` (unbounded). Los bridges (`SimBridge.lean`) validan solo valores concretos via `native_decide`. Para probar corrección para **todos** los inputs de un campo:
- Necesario: teorema `∀ x : Fin p, field_op x ≡ lean_op x [MOD p]`
- Esto requiere extensión de SimBridge o un typeclass `VerifiedField` que encapsule las propiedades
- Pragmático: `native_decide` sobre suficientes valores de boundary + random testing

### Poseidon CodeGen (1,124 LOC)

El módulo más grande de Path B. TrustLean no tiene soporte específico para Poseidon. Opciones:
1. Reformular como `ExpandedSigma` (la MDS matrix multiplication y S-box son componibles)
2. Mantener como UNTRUSTED con tests de compilación
3. Crear frontend TrustLean específico para Poseidon (alto esfuerzo)

Recomendación: Opción 2 corto plazo, opción 1 medio plazo.
