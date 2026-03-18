# Insights: Port de CompletenessSpec de OptiSat a amo-lean

**Fecha**: 2026-03-03
**Dominio**: lean4
**Estado del objeto**: upgrade (amo-lean v2.5.0 → v2.5.1)

## 1. Análisis del Objeto de Estudio

La tarea requiere adaptar la solución probada de **OptiSat v1.5.1 (CompletenessSpec.lean, 425 LOC, 9 declaraciones, 0 sorry)** a **amo-lean v2.5.0 (v4.26.0)** para cerrar dos gaps críticos en el e-graph extraction verificado:

- **G1: DAG acyclicity de bestNode** — no existe prueba formal de que los punteros bestNode formen un DAG acíclico tras `computeCostsF`
- **G2: Fuel sufficiency para extractAuto** — `extractAuto` usa `numClasses + 1` como fuel sin teorema de suficiencia

OptiSat proporciona la estrategia completa y probada:
```
BestCostLowerBound + positive costFn
  → bestCostLowerBound_acyclic (ranking via bestCostOf)
    → extractF_of_rank (strong induction on rank)
      → extractAuto_complete
```

### Diferencias de tipos OptiSat vs amo-lean

| Concepto | OptiSat | amo-lean | Adaptación |
|----------|---------|----------|-----------|
| Op type | `{Op : Type} [NodeOps Op]` genérico | Idéntico (CircuitNodeOp como instancia) | Copia directa |
| ENode, EClass, EGraph | Core.lean | Core.lean (copy de VE) | Nombres idénticos |
| extractF firma | `extractF (g : EGraph Op) (id : EClassId) : Nat → Option Expr` | Idéntico en Greedy.lean | Copia directa |
| extractAuto | `extractAuto g rootId := extractF g rootId (g.numClasses + 1)` | Idéntico en Greedy.lean | Copia directa |
| BestNodeInv | `∀ cid cls nd, classes.get? cid = some cls → cls.bestNode = some nd → nd ∈ cls.nodes.toList` | Idéntico en Core.lean | Copia directa |
| EvalExpr | `EvalExpr Expr Val` con env : `Nat → Val` | `EvalExpr Expr Env Val` genérico sobre Env | **Adaptar** firmas |
| computeCostsF | processKeys + computeCostsLoop + SelfLB | Posiblemente HashMap.fold single pass | **Verificar** implementación |
| Imports | `import LambdaSat.Extractable` | `import AmoLean.EGraph.VerifiedExtraction.Core` | Namespace change |

### Keywords técnicos
BestNodeChild, AcyclicBestNodeDAG, BestCostLowerBound, bestCostLowerBound_acyclic, SelfLB, processKeys_preserves_SelfLB, computeCostsLoop_selfLB, computeCostsF_acyclic, extractF_of_rank, extractAuto_complete, mapOption_some_of_forall, foldl monotonicity, rank function, fuel sufficiency, positive cost function

### Prerequisitos confirmados en amo-lean
Todos los prerequisitos fundamentales YA EXISTEN: UnionFind.WellFormed, ConsistentValuation, BestNodeInv, Extractable typeclass, EvalExpr, ExtractableSound, extractF/extractAuto, mapOption helpers, NodeEval, numClasses, infinityCost, Std.HashMap API (v4.26.0). El port es **add-only** (sin refactorizar Core/Greedy).

## 2. Lecciones Aplicables

### Lecciones reutilizables

| ID | Título | Aplicación al port |
|----|--------|-------------------|
| **L-519** | HashMap Nodup bridge: keys = toList.map Prod.fst + nodup_keys | Probar `(m.toList.map Prod.fst).Nodup` para iteración processKeys |
| **L-520** | omega + struct with-update: pre-compute field projection as rfl | Para inequalities con `{ eclass with bestCost := expr }` patterns |
| **L-521** | Parasitic rewrite in foldl: give equality to omega instead of rw | Fuel bounds + cost inequalities: dar como hypotheses, no rw parasítico |
| **L-434** | omega needs explicit struct hypothesis | omega no reduce struct fields — `have h := p.field; omega` |
| **L-398** | Array.foldl_induction compound invariant | Invariant must include target + WellFormed + structural constraints |
| **L-379** | Disjunctive foldl invariant Q(x) ∈ acc ∨ P(x) | Clasificar nodes en acc como "old" vs "newly added" |
| **L-022** | Strong induction para recursión no-estándar | G2: `Nat.strongRecOn` en rank, no simple induction en fuel |
| **L-471** | extractTreeF: List.mapM with Option monad | Thread Option monad through bestNode recursion |
| **L-501** | Namespace adaptation from VerifiedExtraction | Namespace changes only; zero proof modifications si tipos estructuralmente idénticos |
| **L-371** | Reference proof libraries (copiar/adaptar, NUNCA importar) | Consultar ProofKit/OptiSat ANTES de probar; copiar con namespace adaptado |
| **L-340** | Zero Sorry Discipline: Incremental QA | GATE nodes con `grep -r sorry = 0` ANTES de avanzar |

### Anti-patrones a evitar
1. **Rewriting inside foldl** (L-521): `rw [h_eq]` reescribe parasíticamente en accumulator → representaciones divergentes
2. **Accessing struct fields in omega** (L-434, L-520): omega no reduce `{ s with field := expr }.field`
3. **Simple induction on fuel** (L-022): No funciona para fuel-dependent recursion; usar strong induction
4. **Deferring critical proofs** (L-340): Zero-sorry discipline — NUNCA diferir proofs de acyclicity/fuel
5. **Importing library as lake dependency** (L-371, L-501): Crear acoplamiento; copiar/adaptar localmente

## 3. Bibliografía Existente Relevante

### Documentos clave
| Nombre | Carpeta | Relevancia |
|--------|---------|-----------|
| Goharshady et al. (2024) — Fast and Optimal Extraction for Sparse E-Graphs | egraphs-treewidth | NP-hardness + DAG acyclicity análisis |
| Suciu et al. (ICDT 2025) — Semantic Foundations of Equality Saturation | tensor-optimization | E-graphs ≡ tree automata; fixpoint semántica |
| SmoothE (Cai et al., ASPLOS 2025) | optimizacion | NOTEARS acyclicity enforcement; completeness constraints |
| OptiSat completeness insights | optisat/ | Estrategia probada: level-based acyclicity + fuel monotonicity |

### Insights previos de OptiSat
- `bestCostLowerBound_acyclic` usa bestCostOf como ranking function (13 líneas de prueba)
- `extractF_of_rank` usa strong induction en rank, no en fuel
- HashMap API gap cerrado via `Std.HashMap.keys`/`toList` simp + `nodup_keys` (Lean 4.26)
- 5 helper theorems necesarios: get?_insert_self, get?_insert_ne, keys_nodup, foldl_sum_le_pointwise, processKeys_preserves_SelfLB

### Gaps bibliográficos
- Ningún paper formaliza bestNode DAG acyclicity en proof assistant — OptiSat es el primero
- Fuel sufficiency proofs solo existentes informalmente (egg, egglog)
- Completeness de extraction rara en literatura — papers estudian optimality, no "¿siempre encuentra algo?"

## 4. Estrategias y Decisiones Previas

### Estrategia ganadora de OptiSat v1.5.1
- **Fase 13 (4 bloques, B42-B45)**:
  - B42 (FUND): AcyclicBestNodeDAG definition + bestCostLowerBound_acyclic
  - B43 (PAR): saturateF_preserves_quadruple_internal (hypothesis discharge)
  - B44 (CRIT): extractF_of_rank + extractAuto_complete (strong induction on rank)
  - B45 (HOJA): tests + docs + Path G

### Patrones de ProofKit reutilizables
1. **Foldl Invariant Threading**: `foldl_ge_init`, `foldl_sum_ge_mem` — base para BestCostLowerBound
2. **HashMap Fold Decomposition**: `toList` + `Nodup` — stronger que direct fold reasoning
3. **Option Mapping**: `mapOption_some_of_forall` — base para fuel sufficiency IH
4. **Insert/Get? Bridge**: `get?_insert_self`, `get?_insert_ne` — usado en processKeys proof
5. **Cost Monotonicity**: updateClassBest lower cost doesn't increase lookups

### Convención de bloques en amo-lean
- Fases: `Fase N`, Nodos: `NN.M`, Bloques: `BN` (sequential)
- Última fase: Fase 15 (VerifiedExtraction Integration), último bloque: B59
- **Propuesto**: Fase 16 (Completeness), bloques B60-B62

### Benchmarks de referencia
| Métrica | Fase 15 (amo-lean) | Fase 13 (OptiSat) | Target (Fase 16) |
|---------|--------------------|--------------------|------------------|
| New LOC | 914 | ~670 | 400-500 |
| New theorems | 17 | 7 | 7-10 |
| Sorry | 0 | 0 | 0 |
| Axioms | 0 | 0 | 0 |

## 5. Nueva Bibliografía Encontrada

Sección omitida (--skip-online) — bibliografía existente cubre el tema adecuadamente.

## 6. Insights de Nueva Bibliografía

Sección omitida (sin descargas nuevas).

## 7. Síntesis de Insights

### Hallazgos clave

1. **Port es LOW RISK, HIGH VALUE**: 425 LOC fuente, todos los prerequisitos existen en amo-lean, tipos structuralmente idénticos con minor adaptaciones (Env genérico)
2. **Estrategia probada**: OptiSat cerró G1+G2 con 0 sorry en 4 bloques; la misma estructura DAG aplica directamente
3. **HashMap API gap ya resuelto**: Lean 4.26 tiene `Std.HashMap.nodup_keys` — la misma solución de OptiSat (L-519) se copia verbatim
4. **El port es add-only**: Crear `CompletenessSpec.lean` nuevo sin modificar Core.lean ni Greedy.lean
5. **Strong induction on rank (no fuel)**: Patrón clave — `extractF_of_rank` prueba por inducción fuerte en rank, derivando fuel sufficiency como corolario
6. **3 lecciones críticas** (L-519, L-520, L-521) capturan exactamente los patrones difíciles del proof
7. **Única adaptación real**: EvalExpr usa `Env` genérico en amo-lean vs `Nat → Val` en OptiSat — pero `extractF_of_rank` no depende de Env (solo de `Extractable.reconstruct`)
8. **computeCostsF implementation check necesario**: Verificar si amo-lean tiene processKeys/computeCostsLoop o usa fold single-pass; esto determina si se copian 100% de los theorems o se adaptan

### Riesgos identificados

| Riesgo | Prob. | Impacto | Mitigación |
|--------|-------|---------|-----------|
| computeCostsF diverge de OptiSat | MEDIO | ALTO | Verificar impl antes de copiar theorems; si diverge, reprobar BestCostLowerBound directamente |
| Namespace conflicts | BAJO | BAJO | Usar `AmoLean.EGraph.VerifiedExtraction` namespace (ya establecido) |
| omega con struct projections | MEDIO | BAJO | L-520 pattern probado: `have h := rfl` antes de omega |
| Parasitic rw en foldl | MEDIO | MEDIO | L-521 pattern: dar equalities como hypotheses |

### Recomendaciones para planificación

1. **Fase 16 con 3 nodos + 1 hoja**: N16.1 (FUND: defs + acyclicity), N16.2 (CRIT: fuel sufficiency), N16.3 (HOJA: integration + tests + docs)
2. **De-risk N16.1 primero**: verificar computeCostsF implementation en amo-lean antes de copiar processKeys theorems
3. **Scope estricto**: Solo G1 + G2 en Fase 16; G3 (hypothesis discharge) diferido a Fase 17
4. **Version target**: v2.5.1 (incremento minor)

### Recursos prioritarios
1. **OptiSat/LambdaSat/CompletenessSpec.lean** — código fuente a portar (425 LOC)
2. **L-519, L-520, L-521** — lecciones del cierre del gap
3. **amo-lean/AmoLean/EGraph/VerifiedExtraction/Core.lean** — verificar computeCostsF impl
4. **amo-lean/AmoLean/EGraph/VerifiedExtraction/Greedy.lean** — extractF firma y helpers
5. **ProofKit foldl patterns** — referencia para invariant threading
