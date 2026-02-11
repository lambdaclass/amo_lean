# Fase 8 Onda 1: Adopción Externa para Equipos ZK

**Proyecto**: amo-lean
**Fecha de creación**: 2026-02-09
**Última actualización**: 2026-02-11
**Estado**: 5/5 subfases completadas — lowering_kron_axiom PROVEN (0 sorry)

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
├── Subfase 3: C1 — Kron Verification [COMPLETADA] ✓
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
│   ├── Capa 2: adjustBlock/Stride + lowering_kron_axiom [COMPLETADA] ✓
│   │   ├── HasNoCompose predicate ✓
│   │   ├── IsWellFormedNTT kron strengthened (+ HasNoCompose) ✓
│   │   ├── evalKernelAlg_length ✓
│   │   ├── evalSigmaAlg_loop_preserves_wm_size_with_bound ✓
│   │   ├── adjustBlock_lower_preserves_size ✓
│   │   ├── adjustStride_lower_preserves_size ✓
│   │   ├── lower_preserves_size_ge ✓
│   │   ├── evalSigmaAlg_writeMem_size_preserved kron: I⊗B ✓, A⊗I ✓, A⊗B ✓
│   │   ├── lowering_kron_axiom: I⊗B (non-zero + zero) ✓
│   │   ├── lowering_kron_axiom: A⊗I non-zero (stride scatter assembly) ✓
│   │   ├── lowering_kron_axiom: A⊗I zero (mirror of I⊗B zero) ✓
│   │   └── lowering_kron_axiom: 0 sorry — ALL 19/19 cases PROVEN ✓
│   │
│   └── Capa 3: N/A — writeMem_irrelevant ya resuelto en sesiones anteriores ✓
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
| Subfase 3: C1 Kron Verification | COMPLETADA | 100% | pendiente |
| Subfase 3 C1 Capa 1 | COMPLETADA | 100% | 071d2cf |
| Subfase 3 C1 Corrección 1 | COMPLETADA | 100% | 071d2cf |
| Subfase 3 C1 Capa 2 | COMPLETADA | 100% | pendiente |
| Subfase 3 C1 Capa 3 | COMPLETADA (N/A) | 100% | — |
| Subfase 4: A2 Rust Codegen | COMPLETADA | 100% | 7bd9878 |
| Subfase 5: B1 Radix-4 | COMPLETADA | 100% | 7bd9878 |

---

## DAG de Dependencias

```
lowering_kron_axiom ✓ [COMPLETADO — 0 sorry, ALL 19/19 cases PROVEN]
    ├── evalSigmaAlg_writeMem_size_preserved (kron) ✓
    │   ├── adjustBlock_lower_preserves_size ✓
    │   │   ├── evalScatter_block_size_preserved ✓ (C1 Capa 1)
    │   │   ├── evalKernelAlg_length ✓ (C1 Capa 2)
    │   │   └── evalSigmaAlg_loop_preserves_wm_size_with_bound ✓ (C1 Capa 2)
    │   ├── adjustStride_lower_preserves_size ✓
    │   │   ├── evalScatter_stride_size_preserved ✓ (C1 Capa 1)
    │   │   └── evalSigmaAlg_loop_preserves_wm_size_with_bound ✓ (compartido)
    │   └── lower_preserves_size_ge ✓
    │
    ├── evalSigmaAlg_writeMem_irrelevant (kron) ✓ (sesiones anteriores)
    │
    ├── I⊗B: non-zero + zero ✓ (sesión S-4)
    ├── A⊗I: non-zero (stride scatter assembly) + zero ✓ (sesión S-6)
    └── A⊗B: unreachable (exfalso) ✓ (sesión S-6)
```

**Todos los nodos**: COMPLETADOS
**lowering_kron_axiom**: 0 sorry — PROVEN
**Onda 2**: No necesaria — el objetivo de Onda 2 se completó dentro de Onda 1

---

## Entregables

| ID | Entregable | Objetivo | Estado |
|----|-----------|----------|--------|
| E3 | Sorry cleanup (Theorems.lean) | Credibilidad: reducir sorry count | ✓ COMPLETADO |
| A1 | BabyBear field | Ecosistema: Risc0/SP1 | ✓ COMPLETADO |
| A2 | Rust codegen backend | Ecosistema: integración nativa | ✓ COMPLETADO |
| B1 | Radix-4 C codegen | Performance: butterfly4 kernel | ✓ COMPLETADO |
| C1 | Kron verification (lowering_kron_axiom) | De-risk: lowering correctness | ✓ COMPLETADO |

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

**Onda 2 ya no es necesaria**. El objetivo original de Onda 2 (cerrar `lowering_kron_axiom`) se completó dentro de Onda 1.

| Sorry | Teorema | Estado |
|-------|---------|--------|
| S1 | evalSigmaAlg_writeMem_size_preserved (kron) | ✓ CERRADO |
| S3 | evalSigmaAlg_writeMem_irrelevant (kron) | ✓ CERRADO (sesiones anteriores) |
| S4 | lowering_kron_axiom | ✓ CERRADO — ALL 19/19 cases PROVEN |

**Resultado**: `lowering_kron_axiom` tiene 0 sorry. El teorema principal de correctness del lowering de Kronecker products está formalmente demostrado.

**Sorry restantes en el proyecto** (pre-existentes, no relacionados con Onda 1):
- `AmoLean/FRI/Merkle.lean` — Merkle tree verification (scope diferente)
- `AmoLean/FRI/Poseidon_Semantics.lean` — Poseidon hash semantics (scope diferente)
- `AmoLean/NTT/BabyBear.lean` — BabyBear NTT tests (oracle tests, no teoremas)

---

## Lecciones Aplicadas

- **L-134 a L-138**: DAG de de-risking (orden topológico)
- **L-143**: evalSigmaAlg NO monótona en writeMem.size por .temp
- **L-144**: Precondiciones precisas > monotonía — HasNoCompose es la precondición
- **L-148 a L-152**: foldl_invariant_mem, List.fst_lt_of_mem_enum, dsimp projections, size_write_eq transport, delegation pattern
- **L-153 a L-162** (C1 Capa 2):
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
- **L-176 a L-181** (NUEVAS — C1 Capa 2 final, lowering_kron_axiom PROVEN):
  - L-176: congrArg como alternativa a rw cuando simp transforma el pattern
  - L-177: getElem? (Option) vs getElem (dependent) — trabajar a nivel Option evita "motive not type correct"
  - L-178: Cadena getD ↔ getElem: get?_eq_getElem? + getElem?_eq_getElem + getD_some
  - L-179: Nat.mul_div_cancel (a*b/b=a) vs Nat.mul_div_cancel_left (b*a/b=a)
  - L-180: Option.some.injEq via simp only para inyectividad robusta
  - L-181: adjustStride .nop = .nop es definitionally true — no necesita lema

---

## Criterios de Éxito

- [x] E3: sorry count reducido (Theorems.lean deprecated)
- [x] A1: BabyBear field con NTTField instance + oracle tests
- [x] A2: Rust codegen genera código compilable
- [x] B1: Radix-4 butterfly4 integrado en pipeline
- [x] C1: lowering_kron_axiom PROVEN — ALL 19/19 cases, 0 sorry
- [x] Sorry en AlgebraicSemantics.lean: 0 sorry-using declarations

---

*Creado: 2026-02-09 (post commit 071d2cf)*
*Actualización: 2026-02-10 — C1 Capa 2 ~85% (kron I⊗B, A⊗I, A⊗B cerrados; 10 sorry residuales)*
*Actualización: 2026-02-11 — lowering_kron_axiom PROVEN (0 sorry). Onda 1 COMPLETADA al 100%.*
