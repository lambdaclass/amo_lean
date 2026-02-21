# Insights: AMO-Lean v2.2.0 Trust-Lean Wiring

**Fecha**: 2026-02-21
**Dominio**: lean4
**Estado del objeto**: upgrade

## 1. Análisis del Objeto de Estudio

### Resumen

AMO-Lean v2.2.0 integrará el bridge verificado Trust-Lean v1.2.0 mediante: (1) agregar Trust-Lean como lake dependency, (2) módulo de conversión `AmoLean.Bridge.TrustLean` con funciones `convertExpandedSigma` y `convertScalarVar` que mapean tipos nativos de amo-lean a wrapper types de Trust-Lean, (3) roundtrip lemma demostrando que la conversión preserva estructura, (4) pipeline end-to-end verificado MatExpr → ExpandedSigma → TrustLean.Stmt → código C via CBackend industrial, (5) composición de pruebas AlgebraicSemantics + expandedSigmaToStmt_correct para correctness end-to-end.

### Keywords

1. Bridge type translation — mapeo injective ScalarVar ↔ VarName
2. ExpandedSigma IR — intermediate representation con kernels expandidos
3. TrustLean.Stmt — 12-constructor IR with fuel-based evaluation
4. Verified code generation — pipeline MatExpr → Stmt → C con proofs end-to-end
5. VarName injectivity — kindTag + Int.ofNat para particionamiento seguro
6. Roundtrip correctness — preservación de estructura bajo conversión bidireccional
7. LowLevelEnv semantics — low-level runtime environment con bridge predicates
8. AlgebraicSemantics composition — extensión para incluir Bridge correctness
9. Lake dependency management — integración Trust-Lean como paquete verificado
10. CBackend industrial — sanitización higiénica, paréntesis agresivos (Trust-Lean v1.2.0)
11. Scatter/Gather operations — memory abstraction con índices afines
12. Fuel monotonicity — evalStmt_fuel_mono como firewall crítico
13. Typeclass infrastructure — CodeGenerable + CodeGenSound + BackendEmitter
14. Semantic equivalence — denotational semantics preservation across compilation tiers

### Estado

**upgrade** — Integración de dos sistemas maduros (amo-lean v2.1.0 + Trust-Lean v1.2.0) con arquitectura predefinida. Requiere: nueva capa de bridge, composición de proofs existentes, zero breaking changes en amo-lean core.

### Gaps Identificados

1. **Especificación formal de conversión ScalarVar**: amo-lean usa `name : String` ("x","y","t"), Trust-Lean usa `kind : ScalarVarKind` (.input,.output,.temp). Mapeo injective requiere que strings sean fijos por construcción.
2. **Correctness composition**: ¿Cómo se componen AlgebraicSemantics (5,739 LOC) + Bridge.Correctness en un único teorema end-to-end?
3. **Memory model alignment**: amo-lean usa `mem : Nat → Int` (flat array), Trust-Lean usa `LowLevelEnv : VarName → Value`. Bridge predicates (scalarBridge, loopBridge, memBridge) deben conectar ambos.
4. **Loop fuel binding**: ExpandedSigma.loop(n) recursivo → Trust-Lean while consume fuel. Relación depth ↔ fuel bound.
5. **Parallelism semantics**: `.par` tratado como secuencial en ambos v1.x/v2.x — documentar decisión.
6. **Type universe**: Trust-Lean Value = int Int | bool Bool. amo-lean usa Int para campos finitos (Goldilocks). ¿Suficiente o requiere extensión?

### Dependencias

- **amo-lean v2.1.0**: Lean 4.26.0, Mathlib v4.26.0. NTT + FRI + AlgebraicSemantics (5,739 LOC, zero sorry).
- **Trust-Lean v1.2.0**: CBackend industrial, 12-constructor Stmt IR, fuel-based evaluator, 3 frontends, Bridge wrapper types. 0 sorry.
- **Mathlib v4.26.0**: Resolvido en ambos proyectos.

## 2. Lecciones Aplicables

### Lecciones reutilizables

| ID | Título | Resumen | Categoría |
|----|--------|---------|-----------|
| L-787 | ExpandedSigma bridge success via isomorphism layer FIRST | Establecer wrapper types + inyectividad + disjuntividad PRIMERO. Zero VarName bugs en 1659 LOC. | tacticas §74 |
| L-315 | Three-part bridge predicate enables modular update preservation | Split bridge en scalarBridge + loopBridge + memBridge. Preservación modular por disjuntividad. | tacticas §74 |
| L-337 | Correctness proofs: compositional via helper lemmas | Factorizar cada constructor en lemma separado (~200 LOC máx). Bottom-up: operaciones atómicas → seq/loop/temp. | tacticas §74 |
| L-338 | Fuel bounds: compositional via max not sum | Fuel compone via max, no +. Sequential composition mantiene fuel pequeño. | tacticas §74 |
| L-134–L-138 | Framework DAG de De-Risking | DAG obligatorio. Clasificar FUNDACIONAL > CRÍTICO > PARALELO > HOJA. De-risk fundacional con sketch. | tacticas §65 |
| L-060 | Meta-lemma para casos compute contiguos | Un lema cubre múltiples casos similares de lowering. | arquitectura §28 |
| L-062 | Semántica de .seq y state threading | Clave para composición de evaluaciones. | arquitectura §28 |
| L-066 | Bridge lemmas memory ↔ list | Array.toList_setIfInBounds, Array.size_setIfInBounds. | arquitectura §28 |
| L-071 | Memory roundtrip pattern | `Memory.ofList_toList` como identidad clave para roundtrip lemmas. | induccion §30 |
| L-076 | Axiomas fundacionales vs monolíticos | N axiomas pequeños auditables > 1 axioma opaco. | arquitectura §31 |
| L-078 | Statement más fuerte = IH más fuerte | Generalizar statement para IH reutilizable. | tacticas §32 |
| L-054 | Integración bottom-up de módulos | Proceso mecánico: error bottom → corregir → verificar → subir. | arquitectura §27 |

### Anti-patrones a evitar

1. **Diferir nodos FUNDACIONALES como debt** (L-138): costo de rework multiplicativo
2. **Axiomas monolíticos y opacos** (L-076): 4-5 axiomas pequeños > 1 axioma grande
3. **Múltiples typeclass instances** (L-011): instance diamonds en integración cross-project
4. **Pattern matches incompletos** (L-055): al agregar constructores, TODOS los matches deben actualizarse
5. **Composición sin descomposición** (L-337): factorizar en helpers <200 LOC
6. **Fuel composition aditivo** (L-338): usar max, no sum
7. **simp bare** (L-F9-007): siempre `simp only [lista]`, nunca `simp` sin argumentos

## 3. Bibliografía Existente Relevante

### Documentos clave

| Documento | Carpeta | Resumen |
|-----------|---------|---------|
| CompCert (Leroy 2016) | verificacion | Optimizing compiler verificado C → x86; semantic preservation |
| Accelerating Verified-Compiler Development (Gross 2022) | verificacion | Framework Coq para verified compilers; algebraic rewrite rules |
| HEC: Equivalence Verification (Yin 2025) | verificacion | Verificación post-transformación via e-graphs + MLIR |
| LLMLIFT: Verified Code Transpilation (Bhatia 2024) | verificacion | LLM-based verified lifting con proofs de equivalencia |
| Lean 4 Comprehensive Survey (Tang 2024) | verificacion | Arquitectura, type system, metaprogramming |
| Plonkify R1CS-to-Plonk (Zhu 2025) | criptografia | Compilador verificado entre constraint systems |

### Gaps bibliográficos

1. **Inter-framework proof composition**: composición formal de pruebas ENTRE sistemas distintos
2. **Dynamic bridge maintenance**: correctness de bridges bajo evolución de componentes
3. **Type-level cross-framework integration**: type-safe abstractions multitarget

## 4. Estrategias y Decisiones Previas

### Estrategias ganadoras

| Estrategia | Proyecto | Resultado |
|-----------|---------|-----------|
| Wrapper types vs lake dep directa | Trust-Lean v1.1.0 | Compilación independiente, 0 sorry |
| Constructor-based VarName partitioning | Trust-Lean v1.0.0 | Injectivity gratis por constructor disjointness |
| Two-part bridge predicate | Trust-Lean Fase 6 | Modularidad: scalar + loop probados independientemente |
| Explicit recursion > foldl | Trust-Lean ScalarTranslation | Inducción estándar funciona out-of-the-box |
| Fuel = depth bound (max, no sum) | LeanScribe → Trust-Lean | evalStmt_fuel_mono simple y composable |
| Mathlib CommRing sobre custom typeclasses | SuperTensor Fase 5 | 5 de 7 sorry cerrados al usar Mathlib |
| Zero-sorry guarantee + axiom inventory | Trust-Lean v1.2.0 | 0 sorry, 0 axiom, 244 declarations |

### Decisiones arquitecturales aplicables

1. **Core IR inheritance**: Trust-Lean Stmt (12 constructores) es estable — bridge mapea a él, no lo redefine
2. **Bridge correctness en 3 niveles**: expression homomorphism (GATE) → statement translation → capstone theorem
3. **Wrapper types con compilación independiente**: Trust-Lean v1.2.0 freeze, AMO bridge v2.2.0 hace la conversión
4. **Composición fuel**: seq → max(depths), loop(n) → fuel ≥ n

### Benchmarks de referencia

| Proyecto | LOC | Build | Sorry | Axioms | Theorems |
|----------|-----|-------|-------|--------|----------|
| Trust-Lean v1.2.0 | ~3,400 | <6s | 0 | 0 | 179+ |
| AMO-Lean v2.1.0 | 32,650 | <120s | 0 | 12 | — |
| VR1CS-Lean v1.3.0 | 16,165 | <90s | 0 | 0 | 318 |
| LambdaSat-Lean v0.1.0 | 6,241 | <20s | 0 | 0 | 181 |

**Target v2.2.0**: ~200-400 LOC nuevo (bridge module), 0 sorry, 0 new axioms, <8s incremental build.

### Errores evitados

1. **Monolithic bridge function**: decomposed into 6 composable functions (Trust-Lean Fase 7)
2. **Direct lake dep sin versioning**: wrapper types primero (Trust-Lean v1.1.0)
3. **Fuel como consumed resource**: depth bound con max (LeanScribe precedent)
4. **simp bare en proofs cross-version**: always `simp only [...]` (L-F9-007)
5. **Skipping design spec**: bridge_insights.md escrito ANTES de implementar (Trust-Lean Fase 6)

## 5. Investigación Online

### 5.1 Lake Cross-Project Dependencies

**Sintaxis para dependencia git con tag:**
```lean
-- lakefile.lean
require "org" / "Trust-Lean" @ git "v1.2.0"

-- Desarrollo local (antes de push):
require trustlean from ".." / "Trust-Lean"
```

**Workflow de integración:**
1. Sincronizar `lean-toolchain` entre ambos proyectos (CRÍTICO — Lake compara y falla si incompatibles)
2. Usar tag, no branch, para reproducibilidad
3. Commit `lake-manifest.json` al repo (pins transitivos por hash)
4. `lake update` obligatorio después de cambiar lakefile (build sin update usa versión stale)
5. Nuclear option para conflictos: `rm lake-manifest.json .lake/ && lake update && lake build`

**Fuentes:** Lake README, Mathlib wiki "Using mathlib4 as a dependency", Lean 4 reference docs

### 5.2 Equiv para Isomorfismo de Tipos

Mathlib provee `Equiv` (`α ≃ β`) como patrón canónico para bridges entre tipos:
```lean
structure Equiv (α : Sort u) (β : Sort v) where
  toFun    : α → β
  invFun   : β → α
  left_inv  : LeftInverse invFun toFun   -- invFun (toFun a) = a
  right_inv : RightInverse invFun toFun  -- toFun (invFun b) = b
```

API clave: `Equiv.refl`, `Equiv.symm`, `Equiv.trans`, `Equiv.injective`, `Equiv.bijective`.
Transporte de instancias: `Equiv.inhabited` transporta instancias a lo largo de equivalencias.

**Aplicación**: El bridge ScalarVar → TrustLean.ScalarVar puede modelarse como `Equiv` con roundtrip automático.

**Fuente:** Mathlib.Logic.Equiv.Defs

### 5.3 Sistema de Coerciones para Conversión Transparente

```lean
-- Coerción primaria (una dirección)
@[coe] def toTrustLean (v : AmoLean.ScalarVar) : TrustLean.ScalarVar := ...
instance : Coe AmoLean.ScalarVar TrustLean.ScalarVar where coe := toTrustLean
```

**Clases de coerción:**
- `Coe α β`: estándar, soporta encadenamiento transitivo
- `CoeTail α β`: aplicada solo una vez al final (previene loops)
- `CoeDep α x β`: dependiente, cuando solo ALGUNOS valores se pueden convertir

**PITFALL**: Definir `Coe A B` y `Coe B A` simultáneamente puede causar loop en el elaborator via `CoeT` transitivo. Solución: usar `Coe` en una dirección, casting explícito en la otra.

**Fuente:** Lean 4 Reference "Coercing Between Types"

### 5.4 Patrón CompCert: Forward Simulation Composicional

CompCert compone correctness a través de 14+ passes de compilación usando forward simulation:

> Si programa fuente S produce comportamiento B, entonces programa compilado C también produce B.

Composición: `L1 simula L2 ∧ L2 simula L3 → L1 simula L3`.

**Aplicación directa**: El bridge AMO-Lean → Trust-Lean es un pass adicional. La simulación se compone:
1. AlgebraicSemantics (amo-lean) establece correctness de ExpandedSigma
2. convertExpandedSigma preserva semántica (nuevo lemma)
3. expandedSigmaToStmt_correct (Trust-Lean) establece correctness de Stmt
4. CBackend emite C correcto (Trust-Lean v1.2.0)

**Fuentes:** CompCert backend (Leroy), Compositional CompCert (Appel), CertiCoq

### 5.5 Fiat-Crypto Pipeline

Arquitectura de fiat-crypto para code generation verificado:
1. Especificación de alto nivel (álgebra abstracta)
2. Transformación verificada a IR intermedio
3. Pipeline de bounds analysis
4. Code generation a target (C, Rust, Go)

Cada paso tiene proof de correctness que compone con el siguiente. Pipeline parametrizado por módulo y bitwidth.

**Aplicación**: Misma arquitectura — AMO-Lean parametriza por campo finito, Trust-Lean genera C.

### 5.6 Pitfalls Identificados

| Pitfall | Descripción | Mitigación |
|---------|-------------|-----------|
| **Toolchain mismatch** | Lake falla si lean-toolchain difiere entre proyectos | Sincronizar ANTES de integrar |
| **Mathlib diamond** | Ambos dependen de mathlib en versiones distintas | Usar MISMO tag de mathlib |
| **Coercion loops** | `Coe A B` + `Coe B A` = elaborator loop | Una dirección `Coe`, otra explícita |
| **Manifest stale** | Build sin `lake update` usa versión vieja | Siempre `lake update` tras cambio |
| **Namespace collision** | Ambos definen tipos en namespace similar | Namespaces distintos (`TrustLean.*` vs `AmoLean.*`) |
| **Proof term explosion** | Bridge de estructuras algebraicas genera terms enormes | `@[simp]` lemmas + `rfl`-based proofs |

## 6. Insights de Investigación Online

### Hallazgos nuevos incorporados

1. **Usar `require ... @ git "v1.2.0"` con tag** — no branch ni commit hash suelto. `lake-manifest.json` maneja el pinning exacto.

2. **Sincronizar `lean-toolchain` es prerequisito bloqueante** — verificar ANTES de cualquier otra acción.

3. **Mathlib `Equiv` como base formal del bridge** — provee roundtrip proofs gratis (`left_inv`, `right_inv`) + composición via `trans`. Más robusto que funciones de conversión ad-hoc.

4. **Coerciones unidireccionales** — registrar `Coe AmoLean.ExpandedSigma TrustLean.ExpandedSigma` como dirección primaria. Reversa via `Equiv.symm` explícito.

5. **CompCert forward simulation** es el patrón exacto para componer AlgebraicSemantics + bridge + expandedSigmaToStmt_correct + CBackend.

6. **Development workflow**: usar `require trustlean from ".." / "Trust-Lean"` durante desarrollo local, cambiar a git URL antes de release.

## 7. Síntesis de Insights

### Hallazgos clave

1. **Los tipos son 78% idénticos byte a byte** — solo ScalarVar difiere (String name vs ScalarVarKind enum). Conversión es ~150 LOC mecánico.

2. **Trust-Lean ya tiene TODO el bridge probado** — `expandedSigmaToStmt_correct` prueba simulación completa. AMO-Lean solo necesita la capa de conversión de tipos.

3. **Patrón L-787 (isomorphism layer FIRST)** es el precedente exacto — usado en Trust-Lean v1.1.0 con zero bugs en 1659 LOC. Aplicar idénticamente.

4. **La composición de pruebas es lineal, no exponencial** — AlgebraicSemantics → convert → expandedSigmaToStmt_correct → CBackend. Patrón forward simulation de CompCert con composición transitiva.

5. **No se necesitan axiomas nuevos** — toda la maquinaria formal existe en ambos proyectos. Target: 0 new axioms.

6. **Fuel binding es trivial** — ExpandedSigma.loop(n) requiere fuel n, composición via max. Trust-Lean ya probó `evalStmt_fuel_mono`.

7. **Lake dependency es limpia** — ambos proyectos usan Lean 4.26.0 + Mathlib v4.26.0. Usar `require ... @ git "v1.2.0"` con tag. Sincronizar `lean-toolchain` como prerequisito bloqueante.

8. **El codegen no verificado (CodeGen.lean) NO se elimina** — coexiste con el pipeline verificado. Usuarios eligen.

9. **Mathlib `Equiv` provee roundtrip proofs gratis** — `left_inv` + `right_inv` + composición via `trans`. Más robusto que funciones de conversión ad-hoc.

10. **Coerciones unidireccionales evitan loops** — `Coe` en dirección primaria (AmoLean → TrustLean), reversa explícita via `Equiv.symm`.

### Riesgos identificados

| ID | Riesgo | Impacto | Mitigación |
|----|--------|---------|-----------|
| R1 | ScalarVar.name no es exactamente {"x","y","t"} en todos los constructores | MEDIO | Verificar exhaustivamente en Expand.lean antes de implementar |
| R2 | AlgebraicSemantics composition (5.7K LOC) es complejo de conectar | MEDIO | No componer directamente — solo probar que conversión preserva semántica |
| R3 | Memory model mismatch (Nat→Int vs VarName→Value) | BAJO | Trust-Lean bridge predicates ya resuelven esto |
| R4 | Build time increase con nueva lake dep | BAJO | Trust-Lean <6s incremental, total <130s |
| R5 | lean-toolchain mismatch entre proyectos | MEDIO | Verificar sincronización ANTES de integrar |
| R6 | Coercion loops por Coe bidireccional | BAJO | Una dirección Coe, otra explícita |

### Recomendaciones para planificación

1. **Prerequisito bloqueante**: Sincronizar `lean-toolchain` entre ambos proyectos y verificar que `require ... @ git "v1.2.0"` compila sin conflictos con Mathlib.
2. **Scope mínimo**: Solo el módulo de conversión + roundtrip lemma + tests de integración. NO componer AlgebraicSemantics (eso es v2.3.0+).
3. **Estructura**: Un solo archivo `AmoLean/Bridge/TrustLean.lean` (~200-300 LOC). Usar `Equiv` de Mathlib si ambos proyectos lo importan, o funciones directas con roundtrip proofs si se quiere evitar dependencia Mathlib en el bridge.
4. **Coerciones**: Registrar `Coe` solo en dirección AmoLean → TrustLean (dirección del pipeline). Reversa explícita.
5. **DAG simple**: Lake dep → Conversion functions → Roundtrip lemma → Integration tests → Zero sorry audit.
6. **Development workflow**: `require trustlean from ".." / "Trust-Lean"` durante desarrollo local, cambiar a git URL antes de release.
7. **No romper nada**: El codegen existente (CodeGen.lean) permanece intacto. Pipeline verificado es ADICIONAL.

### Recursos prioritarios

1. **L-787**: Isomorphism layer FIRST — patrón probado para este caso exacto
2. **L-315 + L-337**: Three-part bridge + compositional correctness
3. **Trust-Lean/Bridge/Types.lean**: Wrapper types (368 LOC) — referencia de target types
4. **amo-lean/Sigma/Expand.lean**: Source types (596 LOC) — referencia de source types
5. **Trust-Lean/Bridge/Correctness.lean**: expandedSigmaToStmt_correct (490 LOC) — theorem a componer
