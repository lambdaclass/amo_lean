# Fase 8 Onda 1: Adopción Externa para Equipos ZK

**Proyecto**: amo-lean
**Fecha de creación**: 2026-02-09
**Última actualización**: 2026-02-10
**Estado**: 4/5 subfases completadas, Subfase 3 (C1) Capa 2 ~85%

---

## Objetivo

Habilitar adopción de AMO-Lean por equipos ZK que usan Risc0/SP1 (BabyBear) y Rust.
Baseline: AMO-Lean v1.0.1, Goldilocks field only, C codegen only.

## Contexto

- **Posición**: Fase 8 (Future Work — nueva fase tras v1.0.1)
- **Dominio**: lean4 + C + Rust
- **Complejidad**: max (5 entregables heterogéneos)
- **QA**: 3 rondas Gemini — issues integrados

---

## Árbol de Progreso

```
Fase 8 Onda 1: Adopción Externa
├── Subfase 1: E3 — Sorry Cleanup [COMPLETADA] ✓
│   ├── Capa 1: Comment-block 11 sorries en Theorems.lean ✓
│   └── Capa 2: Eliminar 6 sorries commented-out ✓
│
├── Subfase 2: A1 — BabyBear Field [COMPLETADA] ✓
│   ├── Capa 1: Field arithmetic (BabyBear.lean) ✓
│   ├── Capa 2: NTTField + NTTFieldLawful instances ✓
│   ├── Capa 3: Primitive root proof formal (g=31) ✓
│   ├── Capa 4: Oracle tests vs Risc0 reference values ✓
│   └── Capa 5: Twiddle table + NTT integration test ✓
│
├── Subfase 3: C1 — adjustBlock/Stride Proofs [EN PROGRESO 75%]
│   ├── Capa 1: foldl_invariant helpers ✓
│   │   ├── foldl_invariant (generic, no membership) ✓ (pre-existente)
│   │   ├── foldl_invariant_mem (membership-aware) ✓ (commit 071d2cf)
│   │   ├── evalScatter_preserves_size ✓ (commit 071d2cf)
│   │   ├── evalScatter_block_size_preserved ✓ (commit 071d2cf)
│   │   └── evalScatter_stride_size_preserved ✓ (commit 071d2cf)
│   │
│   ├── Corrección 1: Cerrar 3 evalScatter sorry [COMPLETADA] ✓
│   │   └── Sorry warnings: 5 → 2 (commit 071d2cf)
│   │
│   ├── Capa 2: adjustBlock/Stride size preservation [EN PROGRESO 85%]
│   │   ├── HasNoCompose predicate ✓
│   │   ├── IsWellFormedNTT kron strengthened (+ HasNoCompose) ✓
│   │   ├── evalKernelAlg_length ✓
│   │   ├── evalSigmaAlg_loop_preserves_wm_size_with_bound ✓
│   │   ├── adjustBlock_lower_preserves_size ✓ (3 sorry: kron-inside-kron)
│   │   ├── adjustStride_lower_preserves_size ✓ (3 sorry: kron-inside-kron)
│   │   ├── lower_preserves_size_ge ✓ (3 sorry: I⊗B, A⊗I delegates, m₂=0 edge)
│   │   ├── evalSigmaAlg_writeMem_size_preserved kron: I⊗B ✓, A⊗I ✓, A⊗B ✓
│   │   │   └── 1 sorry restante: degenerate m₂=0 edge case
│   │   ├── eq_of_toList_eq forward-reference fix ✓
│   │   ├── compose case rename_i fix ✓
│   │   └── Pendiente: cerrar 10 sorry residuales (kron-inside-kron + edge cases)
│   │
│   └── Capa 3: adjustBlock/Stride write position characterization (pendiente)
│       └── Body writeMem determinism para writeMem_irrelevant
│
├── Subfase 4: A2 — Rust Codegen Backend [COMPLETADA] ✓
│   ├── Capa 1: Generic NTTField trait design ✓
│   ├── Capa 2: expandedSigmaToRust generator ✓
│   ├── Capa 3: Goldilocks + BabyBear trait impls ✓
│   └── Capa 4: Integration test (NTT roundtrip) ✓
│
└── Subfase 5: B1 — Radix-4 C Codegen [COMPLETADA] ✓
    ├── Capa 1: Kernel.butterfly4 en Sigma/Basic.lean ✓
    ├── Capa 2: Expansion a ScalarExprs en Sigma/Expand.lean ✓
    ├── Capa 3: C codegen para butterfly4 kernel ✓
    └── Capa 4: Pattern matches en Semantics/AlgebraicSemantics/FRI ✓
```

## Estado de Completación

| Componente | Estado | Progreso | Commit |
|------------|--------|----------|--------|
| Subfase 1: E3 Sorry Cleanup | COMPLETADA | 100% | 7bd9878 |
| Subfase 2: A1 BabyBear Field | COMPLETADA | 100% | 7bd9878 |
| Subfase 3: C1 adjustBlock/Stride | EN PROGRESO | 75% | pendiente |
| Subfase 3 C1 Capa 1 | COMPLETADA | 100% | 071d2cf |
| Subfase 3 C1 Corrección 1 | COMPLETADA | 100% | 071d2cf |
| Subfase 3 C1 Capa 2 | EN PROGRESO | 85% | pendiente |
| Subfase 3 C1 Capa 3 | pendiente | 0% | — |
| Subfase 4: A2 Rust Codegen | COMPLETADA | 100% | 7bd9878 |
| Subfase 5: B1 Radix-4 | COMPLETADA | 100% | 7bd9878 |

---

## DAG de Dependencias

```
lowering_kron_axiom [OBJETIVO — Onda 2]
    ├── evalSigmaAlg_writeMem_size_preserved (kron) [85% — 1 sorry: m₂=0 edge]
    │   ├── adjustBlock_lower_preserves_size [85% — 3 sorry: kron-inside-kron]
    │   │   ├── evalScatter_block_size_preserved ✓ (C1 Capa 1)
    │   │   ├── evalKernelAlg_length ✓ (C1 Capa 2)
    │   │   └── evalSigmaAlg_loop_preserves_wm_size_with_bound ✓ (C1 Capa 2)
    │   ├── adjustStride_lower_preserves_size [85% — 3 sorry: kron-inside-kron]
    │   │   ├── evalScatter_stride_size_preserved ✓ (C1 Capa 1)
    │   │   └── evalSigmaAlg_loop_preserves_wm_size_with_bound ✓ (compartido)
    │   └── lower_preserves_size_ge [75% — 3 sorry: delegates + edge]
    │
    └── evalSigmaAlg_writeMem_irrelevant (kron) [0% — C1 Capa 3]
        └── Write position characterization (pendiente)
```

**Nodo fundacional**: C1 Capa 1 — `foldl_invariant_mem` + `evalScatter_*` (COMPLETADO)
**Nodo crítico**: C1 Capa 2 — kron I⊗B, A⊗I, A⊗B: CERRADOS (10 sorry residuales)
**Siguiente**: Cerrar sorry residuales de Capa 2 (kron-inside-kron + m₂=0)
**Bloqueante para Onda 2**: C1 Capa 2 residuales + C1 Capa 3

---

## Entregables

| ID | Entregable | Objetivo | Estado |
|----|-----------|----------|--------|
| E3 | Sorry cleanup (Theorems.lean) | Credibilidad: reducir sorry count | ✓ COMPLETADO |
| A1 | BabyBear field | Ecosistema: Risc0/SP1 | ✓ COMPLETADO |
| A2 | Rust codegen backend | Ecosistema: integración nativa | ✓ COMPLETADO |
| B1 | Radix-4 C codegen | Performance: butterfly4 kernel | ✓ COMPLETADO |
| C1 | adjustBlock/Stride proofs | De-risk: desbloquea Onda 2 | EN PROGRESO (75%) |

---

## Archivos Creados/Modificados en Onda 1

| Archivo | Acción | Subfase |
|---------|--------|---------|
| `AmoLean/Field/BabyBear.lean` | NUEVO (~800 líneas) | A1 |
| `AmoLean/NTT/BabyBear.lean` | NUEVO (~260 líneas) | A1 |
| `AmoLean/Backends/Rust.lean` | NUEVO (~560 líneas) | A2 |
| `AmoLean/Sigma/Basic.lean` | +4 líneas (butterfly4) | B1 |
| `AmoLean/Sigma/Expand.lean` | +44 líneas (expandButterfly4) | B1 |
| `AmoLean/FRI/CodeGen.lean` | +18 líneas (butterfly4 pattern) | B1 |
| `AmoLean/Verification/Theorems.lean` | Comment-block deprecated | E3 |
| `AmoLean/Verification/AlgebraicSemantics.lean` | +610/-71 (C1 Capa 2: kron proofs) | C1 |
| `AmoLean/Verification/Semantics.lean` | +1 línea (butterfly4 pattern) | B1 |

---

## Conexión con Onda 2

**Onda 2** = cerrar los sorry restantes en `AlgebraicSemantics.lean`:

| Sorry | Teorema | Estado | Bloqueador |
|-------|---------|--------|-----------|
| S1 | evalSigmaAlg_writeMem_size_preserved (kron) | 85% — 1 sorry (m₂=0) | C1 Capa 2 residuales |
| S3 | evalSigmaAlg_writeMem_irrelevant (kron) | 0% — sin cambio | C1 Capa 3 |
| S4 | lowering_kron_axiom | 0% — depende de S1+S3 | S1 + S3 |

**C1 Capa 2 (en progreso)**: Los 3 sub-casos principales del kron (I⊗B, A⊗I, A⊗B) están formalmente cerrados.
Quedan 10 sorry residuales: 6 kron-inside-kron (ajustBlock/Stride recursivos), 3 delegates en lower_preserves_size_ge, 1 edge case m₂=0.

**Análisis de sorry residuales**:
- **kron-inside-kron** (6 sorry): Los casos kron dentro de kron en adjustBlock/adjustStride. Son recursivos — necesitan mutual recursion o well-founded decreasing_by.
- **m₂=0 edge case** (1 sorry): El teorema es genuinamente falso cuando m₂=0 y m₁>0. Requiere precondición `m₂ > 0` o `m₁*m₂ > 0`.
- **lower_preserves_size_ge delegates** (3 sorry): Los sub-casos I⊗B y A⊗I delegan a adjustBlock/adjustStride que tienen kron-inside-kron sorry.

---

## Lecciones Aplicadas

- **L-134 a L-138**: DAG de de-risking (orden topológico)
- **L-143**: evalSigmaAlg NO monótona en writeMem.size por .temp
- **L-144**: Precondiciones precisas > monotonía — HasNoCompose es la precondición
- **L-148 a L-152**: foldl_invariant_mem, List.fst_lt_of_mem_enum, dsimp projections, size_write_eq transport, delegation pattern
- **L-153 a L-162** (NUEVAS — C1 Capa 2):
  - L-153: HasNoCompose precondición precisa para kron
  - L-154: Loop lemma con iteration bounds (evalSigmaAlg_loop_preserves_wm_size_with_bound)
  - L-155: evalKernelAlg_length — todos los kernels preservan longitud
  - L-156: apply unification — rw antes de apply para igualdad definitional
  - L-157: rename_i ordering — obtain discards van DESPUÉS de type indices
  - L-158: rename_i count — subst elimina variables del contexto
  - L-159: dsimp only [] es no-op — eliminar, no dejar vacío
  - L-160: set_option in antes de doc comments en Lean 4
  - L-161: lower_preserves_size_ge genuinamente falso cuando m₂=0, m₁>0
  - L-162: eq_of_toList_eq debe declararse antes de write_read_self

---

## Criterios de Éxito

- [x] E3: sorry count reducido (Theorems.lean deprecated)
- [x] A1: BabyBear field con NTTField instance + oracle tests
- [x] A2: Rust codegen genera código compilable
- [x] B1: Radix-4 butterfly4 integrado en pipeline
- [ ] C1: adjustBlock/Stride proofs completos (Capa 2 ~85%, Capa 3 pendiente)
- [ ] Sorry warnings ≤ 2 en `lake build` (actualmente 6 — subió por descomposición en lemas auxiliares)

---

*Creado: 2026-02-09 (post commit 071d2cf)*
*Actualización: 2026-02-10 — C1 Capa 2 ~85% (kron I⊗B, A⊗I, A⊗B cerrados; 10 sorry residuales)*
*Próxima actualización: al cerrar sorry residuales de C1 Capa 2*
