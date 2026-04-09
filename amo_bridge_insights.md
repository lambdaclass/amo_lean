# Insights: Bridge Correctness Gap in AMO-Lean E-Graph Verified Engine

**Fecha**: 2027-02-28
**Dominio**: lean4
**Estado del objeto**: upgrade (cerrar gap crítico en proyecto existente v2.4.1)

## 1. Análisis del Objeto de Estudio

### Resumen

AMO-Lean posee un e-graph verificado (pipeline N11.1-N11.5, `full_pipeline_soundness`) que opera sobre `CircuitNodeOp`, verificando preservación de `ConsistentValuation` durante saturación y extracción. El `Bridge.lean` convierte patrones `Expr Int` a `CircuitPattern` para e-matching, y `mkRule` crea `RewriteRule` a partir de expresiones semánticas, pero **no existe teorema que conecte ambos mundos**. Específicamente:

1. No se formalizó la semántica del pattern matching del e-graph
2. No se demostró que `mkRule` preserve la correspondencia entre `eval(Expr)` y `evalOp(CircuitNodeOp)`
3. Los 20 teoremas verificados en `VerifiedRules.lean` operan sobre `Expr Int`, pero nunca se conectan a `SoundRewriteRule` instances

### Keywords

E-graph translation validation, pattern matching semantics, rewrite rule soundness, Expr↔CircuitNodeOp bridge, semantic homomorphism, pattern binding, eval preservation, circuit semantics, rule instantiation, expression pattern conversion, congruence closure, correctness composition, interface specification, verified equality saturation

### Gaps Identificados

1. **Pattern matching semantics**: No formalizado cómo `CircuitPattern` se traduce a e-node matches
2. **Rule instantiation correctness**: No hay teorema de que `mkRule` preserva equivalencia semántica
3. **Substitution semantics**: No formalizada la correspondencia entre substituciones en ambos dominios
4. **10 reglas sin `SoundRewriteRule`**: Los teoremas existen pero no están integrados al engine
5. **Bridge end-to-end contract**: Sin composición formal expr → rules → optimize → result

### Dependencias

- `ConsistentValuation` (SemanticSpec.lean): predicado de corrección semántica
- `SoundRewriteRule` (SoundRewriteRule.lean): bundle regla + prueba de soundness
- `sound_rule_preserves_consistency`: preservación de invariante bajo regla
- `evalOp` (SemanticSpec.lean): evaluador de CircuitNodeOp
- `CircuitNodeOp` (Core.lean): addGate, mulGate, negGate, smulGate, constGate, witness, pubInput

## 2. Lecciones Aplicables

### Lecciones Reutilizables

| ID | Título | Resumen | Aplicación al Bridge |
|----|--------|---------|---------------------|
| **L-234** | AddExprInv — sub-invariante débil recursiva | Cuando invariante fuerte no se preserva recursivamente, factorizar en sub-invariante más débil | Para inducción sobre CircuitExpr que transforma e-graph |
| **L-235** | add_node_consistent workhorse universal | Un solo teorema maneja todos los casos (hit/miss, leaf/non-leaf) | Blueprint para `translateExpr_consistent` |
| **L-236** | nodeEval_canonical puente entre nodo original y canonicalizado | Bajo valuación UF-consistente, NodeEval preserva semántica tras canonicalize | Clave para probar que bridge preserva evaluación |
| **L-043** | Pattern matching en FIRMA elimina axiomas | Pattern matching en firma genera equation lemmas rfl automáticamente | Para `CircuitExpr → CircuitNodeOp` conversion |
| **L-044** | Equation compiler genera splitters con matching en firma | Match interno → no equation lemmas. Match en firma → sí | Evitar axiomas en pattern cases |
| **L-146** | Bridge lemma conecta formas diferentes de operación | Crear lemma puente explícito antes de usarlo en inducción | Para eval ↔ evalOp bridge |
| **L-229** | Factoring pattern: copiar prueba con field directo | Refactorizar tomando parámetro directo para composición | Para modularizar bridge en layers |
| **L-230** | merge_preserves_pmi cierra contrato merge-rebuild | EGraphWF → PMI (merge) → PMI (process) → EGraphWF (rebuild) | Para composición del bridge con pipeline |
| **L-222** | PostMergeInvariant = invariante parcial | Definir invariante parcial que SABE preservarse en merge-rebuild loop | Invariante intermedio del bridge |
| **L-010** | Bridge lemmas conectan representaciones diferentes | Construir bridge lemmas explícitos antes de teorema complejo | Patrón general para todo el módulo |
| **L-237** | Forward preservation chain en recursión aditiva | `.trans` concatenado para propagar valuación a través de IH múltiples | Para composición eval → bridge → evalOp |

### Anti-patrones a Evitar

1. **Asumir input in-bounds siempre** (L-217): Manejar OOB explícitamente en pattern matching
2. **Requerir invariante fuerte recursivamente** (L-234): Factorizar sub-invariante débil
3. **Match interno vs patrón en firma** (L-043): Mover match a firma para generar equation lemmas
4. **Mezclar representaciones sin bridge** (L-010): Crear bridge lemmas ANTES de usarlos
5. **Probar campo fuerte cuando débil se preserva** (L-222): PostMergeInvariant ≠ EGraphWF
6. **No validar patrón matching con prototipo** (L-046): Crear /tmp/proto.lean primero

### Lecciones Críticas (Top 5)

1. **L-234**: Sin sub-invariant factoring, la inducción recursiva sobre e-graph es imposible
2. **L-043-L-047**: Pattern matching en firma elimina axiomas — necesario para 20-case exhaustive match
3. **L-146 + L-229-L-230**: Bridge lemmas + factoring para composición modular
4. **L-235**: Workhorse universal evita explosión combinatoria (1 theorem vs 4-8 lemmas)
5. **L-236**: nodeEval_canonical es el bridge existente que conecta nodos con evaluación

## 3. Bibliografía Existente Relevante

### Documentos Clave

| Documento | Carpeta | Resumen |
|-----------|---------|---------|
| Semantic Foundations of Equality Saturation (Suciu 2025) | tensor-optimization | E-graphs ≈ tree automata rígidos, semántica de punto fijo |
| egg: Fast and Extensible Equality Saturation (Willsey 2021) | egraphs-treewidth | Arquitectura e-graph moderna: rebuilding, congruence closure |
| CompCert (Leroy 2016) | verificacion | Simulation diagrams, semantic preservation mecanizada |
| TensorRight: Automated Verification of Tensor Rewrites (Arora 2025) | tensor-optimization | Semántica denotacional, unbounded verification |
| Colored E-Graphs (Singher 2023) | verificacion | Conditional rewrite rules con soundness |
| Accelerating Verified Compiler (Gross 2022) | verificacion | Framework Coq para pattern-matching compilation |
| HEC: Equivalence Verification Checking (Yin 2025) | verificacion | MLIR functional equivalence via equality saturation |

### Gaps Bibliográficos

1. **Lean 4 e-graph correctness**: No paper formaliza congruence closure en Lean 4 con Mathlib
2. **Pattern language verification**: No semántica denotacional para pattern DSLs verificados
3. **Circuit-arithmetic semantics bridge**: No paper sobre evalOp genérico para e-graph circuits
4. **Pattern binding preserves evaluation**: No formalización mecanizada de este lema

## 4. Estrategias y Decisiones Previas

### Estrategias Ganadoras

| Estrategia | Proyecto Fuente | Resultado |
|------------|----------------|-----------|
| **Three-layer bridge** (type iso → function eq → property preservation) | Trust-Lean v1.2.0 → AMO-Lean Fase 13 | 7 files, 1,606 LOC, 66 theorems, 0 sorry, 0 axioms |
| **Staged Merkle proof** (helpers → inversion → bridge) | VR1CS + OptiSat | 261 LOC, 11 theorems, 0 axioms |
| **Firewall `_aux`** (develop in _aux with sorry, migrate when clean) | SuperTensor + OptiSat | Pioneer HashMap.fold approach, replicated in 3 modules |
| **Precondition audit + auto-discharge** | SuperTensor v3.5.4 | All 5 per-rule hypotheses auto-discharged, 0 sorry |
| **Roundtrip + injectivity** (backward rfl, forward induction) | Trust-Lean v1.2.0 | 544 LOC, 26 theorems, 0 axioms |

### Código Reutilizable de Proyectos Fuente

#### OptiSat (`~/Documents/claudio/optisat/`)
- `SoundRule.lean` (L32-46): `SoundRewriteRule(Op, Expr, Val)` structure — ORIGEN del framework
- `SoundRule.lean` (L104-116): `sound_rule_preserves_consistency` — theorem pattern
- AMO-Lean ya lo adaptó en N11.3 pero sin instanciar con reglas reales

#### SuperTensor-lean (`~/Documents/claudio/SuperTensor-lean/`)
- `TranslationValidation.lean` (L35-61): `tensorEquivalent` predicate + refl/symm/trans
- `TranslationValidation.lean` (L72-206): 14 congruence theorems por constructor
- `SoundRule.lean` (L43-50): `SoundTensorRule` con `sound : ∀ env, lhs.eval = rhs.eval`
- `SoundRule.lean` (L91-125): 3 demo rules (addComm, addAssoc, negNeg) probadas con ring
- Patrón: cada constructor tiene `tensorEquivalent_constructor` theorem

#### VR1CS-lean (`~/Documents/claudio/vr1cs-lean/`)
- `CCSBridge.lean` (L75-86): `isR1CSStructure` check — validates structural invariants
- `CCSBridge.lean` (L160-199): `r1csCCSRowResidual`, `satisfies_r1cs_iff_residuals`
- `CCSBridge.lean` (L208-231): `r1csToCCS_sound` — bidirectional equivalence
- Patrón: residual predicate → relates to satisfaction → proves ↔ equivalence

### Decisiones Arquitecturales Aplicables

1. **Separar correction vs completeness**: Solo probar soundness, no completeness (reducir TCB)
2. **`CryptoEquivalent` como equivalence + congruence**: Definir relación → prove refl/symm/trans → wire congruence para todas las ops
3. **Scope control**: Bridge solo los mismatches críticos, NO todos los 357 defs
4. **Formal properties = P0, Plausible = P1**: Proofs formales para correctness, property tests para edge cases

### Errores Evitados

1. **Monolithic bridge axioms** (SuperTensor v3.5.0): Decompose to per-rule cases
2. **Large extraction bridge** (OptiSat v0.1.0): Decompose to BestNodeInv + 4 check lemmas
3. **Axiom confinement failure** (VR1CS v1.0): Confine axioms to narrowest boundary
4. **Circular dependency** (Trust-Lean v1.0): Prove backward (rfl) then forward (induction) independently
5. **Premature field specialization** (SuperTensor v3.5.1): Prove over generic `[Field F]` first
6. **Over-specification of invariants** (OptiSat v0.1): Minimal invariant set per function

## 5. Nueva Bibliografía Encontrada (Online)

### Papers de Alta Relevancia

| Paper | Venue | Key Insight para AMO-Lean |
|-------|-------|--------------------------|
| **Bridging Syntax and Semantics of Lean Expressions in E-Graphs** (Rossel, Goens, EGRAPHS 2024) | [arXiv:2405.10188](https://arxiv.org/abs/2405.10188) | lean-egg bridge: Lean-Expr → egg nodes. Partial unsoundness tolerada porque kernel verifica resultado final |
| **Towards Pen-and-Paper-Style Equational Reasoning in ITPs** (Rossel et al., POPL 2026) | [DOI:10.1145/3776667](https://dx.doi.org/10.1145/3776667) | Clasificación de precondiciones para conditional rewrite rules. Directamente aplicable a `ConditionalSoundRewriteRule` |
| **Semantic Foundations of Equality Saturation** (Suciu et al., ICDT 2025) | [arXiv:2501.02413](https://arxiv.org/abs/2501.02413) | E-graphs = tree automata rígidos. A lo sumo un homomorfismo entre dos e-graphs → unicidad del bridge |
| **Dis/Equality Graphs** (Zakhour et al., POPL 2025) | [DOI:10.1145/3704913](https://dl.acm.org/doi/10.1145/3704913) | **Primera prueba formal**: e-graph = cierre RSTC (reflexivo, simétrico, transitivo, congruente) |
| **Lean4Lean** (Carneiro, 2024) | [arXiv:2403.14064](https://arxiv.org/abs/2403.14064) | Patrón `Expr → VExpr` via tipo inductivo. Directamente aplicable a `Expr → CircuitNodeOp` |
| **Denotational Semantics of SSA** (Ghalayini, Krishnaswami, 2024) | [arXiv:2411.09347](https://arxiv.org/abs/2411.09347) | Semántica denotacional de IR mecanizada en Lean. Patrón para `evalOp` formalization |

### Repositorios

| Repo | URL | Relevancia |
|------|-----|------------|
| **lean-egg** | [github.com/marcusrossel/lean-egg](https://github.com/marcusrossel/lean-egg) | Táctica de equality saturation para Lean 4. Soundness via proof witness verificado por kernel. 568 commits, activo |
| **lean4lean** | [github.com/digama0/lean4lean](https://github.com/digama0/lean4lean) | Typechecker verificado de Lean en Lean. Patrón Expr→VExpr para bridge |
| **Tesis de Rossel** | [TU Dresden](https://cfaed.tu-dresden.de/files/Images/people/chair-cc/theses/2407_Rossel_MA.pdf) | Descripción técnica más completa de lean-egg internals |

### Insights Clave de la Búsqueda Online

1. **lean-egg resuelve exactamente nuestro problema** pero con translation validation: egg genera proof witness, kernel de Lean verifica. Ni egg ni la táctica están en el TCB. AMO-Lean podría adoptar el mismo approach: bridge no es trusted, resultado final se verifica.

2. **Zakhour (POPL 2025) da la base teórica**: e-graph ≡ cierre RSTC. Nuestro `ConsistentValuation` + merge/find/process preservation es una instancia de esto.

3. **Suciu (ICDT 2025) da unicidad**: a lo sumo un homomorfismo entre dos e-graphs → nuestra traducción, si existe, es canónica.

4. **Lean4Lean `Expr → VExpr`**: patrón directamente reutilizable para `Expr Int → CircuitNodeOp`.

5. **AMO-Lean's `ConsistentValuation` es trabajo original**: no existe otra formalización de congruence closure en Lean 4 con Mathlib.

## 6. Insights de Nueva Bibliografía

Sección omitida (sin descargas de PDFs — búsqueda online solo recopiló metadata).

## 7. Síntesis de Insights

### Hallazgos Clave (Top 10)

**1. El bridge es cerrable con ~400-600 LOC usando patrones probados.**
Los 3 proyectos fuente (OptiSat, SuperTensor, VR1CS) comparten un patrón de 3 capas que AMO-Lean ya usó exitosamente en Fase 13. El bridge de VerifiedRules → SoundRewriteRule sigue exactamente el mismo template.

**2. Estrategia de 4 niveles identificada en los proyectos fuente.**
- Nivel 1: Teoremas algebraicos sobre `Expr Int` (YA EXISTE: 20 theorems)
- Nivel 2: Bridge `eval(Expr) = evalOp(CircuitNodeOp)` (FALTA: ~200 LOC)
- Nivel 3: Adaptar teoremas a `SoundRewriteRule` instances (FALTA: ~200 LOC)
- Nivel 4: End-to-end contract componiendo N1-N3 con pipeline (FALTA: ~100 LOC)

**3. lean-egg (POPL 2026) ofrece un approach alternativo: translation validation.**
En lugar de probar que el bridge es correcto estáticamente, se puede generar un proof witness que el kernel verifica. AMO-Lean ya tiene esto parcialmente con `TranslationValidation.lean`. Pero probar el bridge estáticamente es más fuerte.

**4. SuperTensor tiene el código más reutilizable.**
`TranslationValidation.lean` (14 congruence theorems), `SoundRule.lean` (3 demo rules probadas) son plantillas directas. El patrón `tensorEquivalent_constructor` por constructor = exactamente lo que necesitamos para `Expr.add`, `Expr.mul`, etc.

**5. VR1CS CCSBridge da el blueprint para el bridge semántico.**
El patrón residual → satisfaction → bidirectional ↔ es el esquema exacto para conectar `eval(Expr)` con `evalOp(CircuitNodeOp)`.

**6. `ConsistentValuation` de AMO-Lean es contribución original.**
No existe otra formalización de congruence closure correctness en Lean 4 con Mathlib. El bridge que cerraríamos conectaría las 20 reglas algebraicas con esta formalización original, aumentando significativamente el valor académico.

**7. Pattern matching en firma (L-043) es OBLIGATORIO.**
El bridge requiere un match exhaustivo de 20 reglas. Sin L-043 (match en firma), el equation compiler no generará splitters → necesitará axiomas. Con L-043, cada caso genera equation lemmas automáticamente.

**8. Precondition audit + auto-discharge (SuperTensor v3.5.4) elimina hipótesis externas.**
El master theorem puede tener 0 hipótesis externas si las precondiciones se formalizan y auto-descargan, como demostró SuperTensor.

**9. Los 4 gaps bibliográficos persisten → contribución nueva.**
No existe formalización mecanizada de:
- Pattern binding preserves evaluation
- Pattern DSL denotational semantics
- evalOp/circuit-arithmetic semantics bridge
- Congruence closure en Lean 4

Cerrar el bridge sería trabajo publicable.

**10. El scope es controlable: 20 reglas, no 357 defs.**
Aplicar la lección de Fase 13 (scope control): bridge solo los 20 theorems de VerifiedRules → SoundRewriteRule. No intentar bridgear toda la infraestructura operacional.

### Riesgos Identificados

| Riesgo | Severidad | Mitigación |
|--------|-----------|------------|
| `CircuitNodeOp` no tiene `powGate` → power rules no son bridgeables directamente | MEDIA | Compilar `pow` a cadena de `mulGate`s, o excluir power rules del bridge (son 4 de 20) |
| Constant folding requiere side condition → `ConditionalSoundRewriteRule` | BAJA | Infraestructura ya existe en N11.3 |
| Equation compiler puede fallar con 20-case match | BAJA | Usar match en firma (L-043), validar con prototipo (L-046) |
| `eval(Expr Int)` usa `Int` pero `evalOp` usa genérico `Val` | MEDIA | Bridge parametrizado por `[Add Val] [Mul Val] [Neg Val]`, instanciar con `Int` |
| Bridge puede requerir homomorphism (Suciu) que es difícil de formalizar | BAJA | No necesitamos tree automata completo; solo necesitamos correspondencia eval ↔ evalOp por inducción sobre Expr |

### Recomendaciones para Planificación

**Opción A: Bridge Estático (recomendada, ~500 LOC)**
1. Definir `ExprToCircuit : Expr Int → CircuitNodeOp expression` (conversión formal)
2. Probar `exprToCircuit_eval_eq : eval e env = evalOp (exprToCircuit e) env v` por inducción
3. Instanciar 16 `SoundRewriteRule` (20 teoremas menos 4 power rules)
4. Probar que las 16 instancias satisfacen `PreservesCV`
5. Master theorem: `verified_optimization_with_rules`

**Opción B: Translation Validation Reforzada (~300 LOC)**
Estilo lean-egg: no probar el bridge estáticamente, sino reforzar `TranslationValidation.lean` con:
1. `CryptoEquivalent` congruence theorems para todos los constructores
2. Verificación post-hoc: cada optimización produce witness verificable
3. Menos trabajo formal, pero no cierra el gap teórico

**Opción C: Híbrida (~400 LOC)**
Bridge estático para las 10 reglas ya en `Rules.lean` (addZero, mulOne, etc.), translation validation para el resto. Cierra el gap parcialmente con máximo valor por esfuerzo.

**Recomendación**: Opción A. El esfuerzo es moderado (~500 LOC), cierra completamente el gap, produce contribución publicable, y los patrones están todos probados en proyectos previos.

### Recursos Prioritarios

1. **SuperTensor `TranslationValidation.lean`** — Template para congruence theorems
2. **VR1CS `CCSBridge.lean`** — Blueprint para bridge semántico bidireccional
3. **L-043 a L-047** — Pattern matching en firma (obligatorio para 20-case match)
4. **L-234** — Sub-invariant factoring (si inducción requiere invariante débil)
5. **Zakhour (POPL 2025)** — Base teórica formal para justificar que e-graph = cierre RSTC
