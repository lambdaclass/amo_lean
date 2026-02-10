# Fase 8 Onda 1: Adopción Externa para Equipos ZK

**Proyecto**: amo-lean
**Fecha de creación**: 2026-02-09
**Última actualización**: 2026-02-09
**Estado**: 4/5 subfases completadas, Subfase 3 (C1) en progreso

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
├── Subfase 3: C1 — adjustBlock/Stride Proofs [EN PROGRESO 40%]
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
│   ├── Capa 2: adjustBlock/Stride size preservation (pendiente)
│   │   └── Conectar evalScatter_{block,stride}_size_preserved con loop body kron
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
| Subfase 3: C1 adjustBlock/Stride | EN PROGRESO | 40% | 071d2cf |
| Subfase 3 C1 Capa 1 | COMPLETADA | 100% | 071d2cf |
| Subfase 3 C1 Corrección 1 | COMPLETADA | 100% | 071d2cf |
| Subfase 3 C1 Capa 2 | pendiente | 0% | — |
| Subfase 3 C1 Capa 3 | pendiente | 0% | — |
| Subfase 4: A2 Rust Codegen | COMPLETADA | 100% | 7bd9878 |
| Subfase 5: B1 Radix-4 | COMPLETADA | 100% | 7bd9878 |

---

## DAG de Dependencias

```
Onda 2 (kron correctness final — 3 sorry)
    └── C1 Capa 2: adjustBlock/Stride size preservation
            └── C1 Capa 1: foldl_invariant + evalScatter ✓ (COMPLETADA)

Onda 2 (writeMem_irrelevant kron — 1 sorry)
    └── C1 Capa 3: write position characterization
            └── C1 Capa 1: foldl_invariant + evalScatter ✓ (COMPLETADA)
```

**Nodo fundacional**: C1 Capa 1 — `foldl_invariant_mem` + `evalScatter_*` (COMPLETADO)
**Nodo crítico**: C1 Capa 2 — conectar evalScatter con loop body (SIGUIENTE)
**Bloqueante para Onda 2**: C1 Capas 2-3

---

## Entregables

| ID | Entregable | Objetivo | Estado |
|----|-----------|----------|--------|
| E3 | Sorry cleanup (Theorems.lean) | Credibilidad: reducir sorry count | ✓ COMPLETADO |
| A1 | BabyBear field | Ecosistema: Risc0/SP1 | ✓ COMPLETADO |
| A2 | Rust codegen backend | Ecosistema: integración nativa | ✓ COMPLETADO |
| B1 | Radix-4 C codegen | Performance: butterfly4 kernel | ✓ COMPLETADO |
| C1 | adjustBlock/Stride proofs | De-risk: desbloquea Onda 2 | EN PROGRESO (40%) |

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
| `AmoLean/Verification/AlgebraicSemantics.lean` | +48/-23 (evalScatter proofs) | C1 |
| `AmoLean/Verification/Semantics.lean` | +1 línea (butterfly4 pattern) | B1 |

---

## Conexión con Onda 2

**Onda 2** = cerrar los 3 kron sorry restantes en `AlgebraicSemantics.lean`:

| Sorry | Teorema | Bloqueador de C1 |
|-------|---------|-------------------|
| S1 | evalSigmaAlg_writeMem_size_preserved (kron) | C1 Capa 2 |
| S3 | evalSigmaAlg_writeMem_irrelevant (kron) | C1 Capa 3 |
| S4 | lowering_kron_axiom | S1 + S3 + full correctness |

**C1 Capa 1 (completada)** desbloqueó la infraestructura bottom-up. Falta la conexión top-down (loop body → evalScatter).

---

## Lecciones Aplicadas

- **L-134 a L-138**: DAG de de-risking (orden topológico)
- **L-143**: evalSigmaAlg NO monótona en writeMem.size
- **L-144**: Precondiciones precisas > monotonía
- **L-148 a L-152**: foldl_invariant_mem, List.fst_lt_of_mem_enum, dsimp projections, size_write_eq transport, delegation pattern

---

## Criterios de Éxito

- [x] E3: sorry count reducido (Theorems.lean deprecated)
- [x] A1: BabyBear field con NTTField instance + oracle tests
- [x] A2: Rust codegen genera código compilable
- [x] B1: Radix-4 butterfly4 integrado en pipeline
- [ ] C1: adjustBlock/Stride proofs completos (Capas 2-3 pendientes)
- [ ] Sorry warnings ≤ 2 en `lake build` (actualmente 2 ✓ — pero S1 aún sorry statement)

---

*Creado: 2026-02-09 (post commit 071d2cf)*
*Próxima actualización: al completar C1 Capa 2*
