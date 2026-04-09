# Lecciones Fase 9: Migración Lean 4.16 → 4.26

## Lecciones heredadas (de vr1cs-lean, aplicables a migración)

### L-F9-001: native_decide + proof fields = free variables error
**Origen**: L-199 (vr1cs-lean)
**Contexto**: Al migrar Field/Goldilocks y Field/BabyBear
**Problema**: `native_decide` con ZMod proof fields produce error 'free variables'
**Solución**: Usar `toZMod_injective` bridge. Patrón idéntico entre v4.16 y v4.26.

### L-F9-002: HashMap.fold sin induction principle en v4.26
**Origen**: L-200 (vr1cs-lean)
**Contexto**: Motor E-Graph (EGraph/Basic.lean usa Std.HashMap.fold)
**Problema**: Std/Batteries carecen de `HashMap.fold_induction` o `fold_eq_foldl_toList`
**Solución**: Reescribir como recursión explícita sobre `origHashmap.toList.map Prod.fst` con `get?` lookup

### L-F9-003: by_contra no existe sin Mathlib en v4.26
**Origen**: L-207 (vr1cs-lean)
**Contexto**: Proofs que usen `by_contra` directamente
**Solución**: `rcases Nat.lt_or_ge x y with h | h` → cases on linear order, luego `exfalso`

### L-F9-004: attribute [local irreducible] ANTES de docstring
**Origen**: L-209 (vr1cs-lean)
**Contexto**: E-graph con matches complejos (rebuild, computeCosts)
**Problema**: `(g.add node).2` normaliza a ~15 líneas de match, causando whnf timeout (200K heartbeats)
**Solución**: `attribute [local irreducible] EGraph.add in` ANTES del docstring, no después

### L-F9-005: Docstrings antes de section causan parse error
**Origen**: L-300 (vr1cs-lean)
**Contexto**: Cualquier archivo con `/-- -/` antes de `section Name`
**Solución**: Usar `-- ...` comments en su lugar

### L-F9-006: Port entre versiones — adaptar namespace, no copiar
**Origen**: L-302 (vr1cs-lean)
**Contexto**: Port de UnionFind, CoreSpec, SemanticSpec desde vr1cs-lean
**Lección**: Identificar subconjunto mínimo. Namespace se adapta; runtime wrappers no. Ahorra ~1,390 LOC.

### L-F9-007: simp only preferido sobre simp (full)
**Origen**: Anti-patrón recurrente en ambos proyectos
**Lección**: `simp` (full) es impredecible entre versiones. Usar `simp only [lista]` para comportamiento determinístico. Crítico en migración: un `simp` que funcionaba en 4.16 puede fallar silenciosamente en 4.26.

### L-F9-008: Std.HashMap.empty → nueva API en v4.26
**Origen**: Análisis de impacto amo-lean v2.0.0
**Problema**: `Std.HashMap.empty` ya no existe en 4.26
**Solución**: Usar `Std.HashMap.ofList []` o `.emptyWithCapacity n`

### L-F9-009: HashSet en structs → Array por restricción de universo
**Origen**: Comparación amo-lean (4.16) vs vr1cs-lean (4.26)
**Problema**: `Std.HashSet T` con T en universo > 0 causa error de universo
**Solución**: Reemplazar con `Array T`, usar `.contains` en vez de `.mem`, `.push` en vez de `.insert`

### L-F9-010: Well-founded recursion opaca desde v4.19
**Origen**: Lean 4.19 release notes
**Problema**: Funciones WF recursion no se despliegan con `rfl`. `unseal` inefectivo.
**Solución**: Agregar `@[semireducible]` a la definición, o cambiar estrategia de proof

---

## Lecciones aprendidas durante migración

*(Se irán agregando a medida que trabajemos)*

### L-F9-011: [PENDIENTE]

---

*Última actualización: 2026-02-16*
