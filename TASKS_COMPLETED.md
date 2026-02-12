# AMO-Lean: Estado del Proyecto y Trabajo Completado

**Proyecto**: amo-lean (Automatic Mathematical Optimizer in Lean)
**Fecha**: 2026-02-12
**Versión actual**: post v1.0.1
**Lean**: 4.16.0, Mathlib v4.16.0
**Este es el documento canónico de estado del proyecto.** Cualquier otro roadmap o inventario está archivado en `docs/archive/`.

---

## Resumen Ejecutivo

AMO-Lean es un optimizador formal que transforma especificaciones matemáticas (MatExpr) en código C/Rust optimizado con corrección garantizada por construcción.

**Estado**: El teorema principal de correctness del lowering (`lowering_algebraic_correct`) está formalmente demostrado para todos los constructores de MatExpr relevantes, incluyendo el caso más difícil: Kronecker products (`lowering_kron_axiom` — 0 sorry, ALL 19/19 cases PROVEN). Los 5 axiomas fundacionales de Goldilocks Field fueron eliminados formalmente (Bloque Central, 2026-02-11). Los 4 axiomas de BabyBear Field + 4 sorry de NTT/BabyBear fueron eliminados (2026-02-12).

---

## Fases Completadas (0-5 + 8 Onda 1 + Bloque Central)

| Fase | Descripción | Estado | Fecha |
|------|-------------|--------|-------|
| 0 | Proof of Concept (FRI Fold) | COMPLETADA | 2026-01-28 |
| 1 | Goldilocks Field + E-Graph | COMPLETADA | 2026-01-28 |
| 2 | Reglas de Optimización | COMPLETADA | 2026-01-28 |
| 3 | CodeGen SIMD (AVX2) | COMPLETADA | 2026-01-28 |
| 4 | Empaquetado + Verificación | COMPLETADA | 2026-01-29 |
| 5 | NTT Core (Cooley-Tukey + Radix4) | COMPLETADA | 2026-01-29 |
| 6A | Verificador de Plonky3 | NO INICIADA | — |
| 6B | Generador multi-backend | NO INICIADA | — |
| 8 Onda 1 | Adopción externa ZK + Kron verification | COMPLETADA | 2026-02-11 |
| Bloque Central | Eliminación 5 axiomas Goldilocks | COMPLETADA | 2026-02-11 |
| BabyBear | Eliminación 4 axiomas + 4 sorry BabyBear | COMPLETADA | 2026-02-12 |

### Fase 8 Onda 1: Detalle de Entregables

| ID | Entregable | Descripción | Estado |
|----|-----------|-------------|--------|
| E3 | Sorry cleanup | Theorems.lean deprecated (7 sorry inactivos) | COMPLETADO |
| A1 | BabyBear field | Campo BabyBear (p=2013265921) + NTTField instance | COMPLETADO |
| A2 | Rust codegen | expandedSigmaToRust genera código Rust compilable | COMPLETADO |
| B1 | Radix-4 codegen | butterfly4 kernel integrado en pipeline C | COMPLETADO |
| C1 | Kron verification | lowering_kron_axiom PROVEN — 0 sorry | COMPLETADO |

### Bloque Central: Eliminación de Axiomas Goldilocks

| Bloque | Axioma eliminado | Estrategia | Estado |
|--------|-----------------|------------|--------|
| GATE | `goldilocks_prime_is_prime` | Lucas primality + zpowMod | COMPLETADO |
| 1 | `goldilocks_canonical` | Subtype refactor + 7 sorry eliminados | COMPLETADO |
| 2 | `reduce128_correct` | 6 sub-lemas, descomposición modular | COMPLETADO |
| 3 | `toZMod_pow` | Strong induction + mul_def bridge | COMPLETADO |
| 4 | `toZMod_inv` | Fermat (ZMod.pow_card_sub_one_eq_one) | COMPLETADO |

**Detalle completo**: `Bloque_central_plan.md`

---

## Inventario Completo de Sorry y Axiomas

**Fecha de auditoría**: 2026-02-12 (verificado por `grep` sobre código fuente)

### Resumen Cuantitativo

| Categoría | Cantidad | Archivos |
|-----------|----------|----------|
| **Sorry activos** | **14** | Poseidon(12), Merkle(2) |
| **Sorry comentados (inactivos)** | **13** | Theorems(7), Perm(4), Spec(1), Properties(1) |
| **Axiomas activos** | **12** | NTT(11), Perm(1) |

### A. Sorry Activos (14)

#### A.1. Poseidon_Semantics.lean — 12 sorry (ADR-006: computationally verified)

**Naturaleza**: Match splitter limitation de Lean 4. Los 12 sorry son demostrables en principio pero Lean no puede generar splitters automáticos para pattern matching recursivo profundo sobre indexed inductives.

**Verificación**: 21 tests computacionales pasan (100% coverage).

**DAG de dependencias**:
```
Phase B (fundamental — match splitter):
  elemwise_pow_correct ─────────────┐
  mdsApply_external_correct ────────┤
  addRoundConst_correct ────────────┼──→ fullRound_equiv ──────┐
  mdsApply_internal_correct ────────┤                          │
  partialElemwise_correct ──────────┼──→ partialRound_equiv ───┤
  compose_correct                   │                          │
                                    │                          ▼
Phase C (composición):              │    fullRound_components ─┐
                                    │    partialRound_comp. ───┤
                                    │                          ▼
Phase D (teorema principal):        │    poseidon2_correct ────┤
                                    │    poseidon2_hash_correct┘
```

| # | Teorema | Línea | Bloqueador | Dificultad |
|---|---------|-------|-----------|------------|
| 1 | `elemwise_pow_correct` | 472 | Match splitter | MEDIA |
| 2 | `mdsApply_external_correct` | 491 | Match splitter + strings | MEDIA |
| 3 | `mdsApply_internal_correct` | 502 | Match splitter + strings | MEDIA |
| 4 | `addRoundConst_correct` | 515 | Match splitter | MEDIA |
| 5 | `partialElemwise_correct` | 535 | Match splitter | MEDIA |
| 6 | `compose_correct` | 560 | Match splitter recursivo | MEDIA-ALTA |
| 7 | `fullRound_equiv` | 766 | Depende de 1,2,4 | MEDIA |
| 8 | `partialRound_equiv` | 789 | Depende de 3,4,5 | MEDIA |
| 9 | `fullRound_components_correct` | 803 | Depende de 7 | BAJA |
| 10 | `partialRound_components_correct` | 817 | Depende de 8 | BAJA |
| 11 | `poseidon2_correct` | 986 | Fold induction sobre 9,10 | MEDIA-ALTA |
| 12 | `poseidon2_hash_correct` | 998 | Corolario de 11 | BAJA |

**Impacto**: Aislado. No afecta AlgebraicSemantics ni NTT. Solo importa para la verificación end-to-end de Poseidon2.

#### A.2. FRI/Merkle.lean — 2 sorry (size invariants)

| # | Teorema | Línea | Descripción | Dificultad |
|---|---------|-------|-------------|------------|
| 1 | `h_size` (buildTree) | 279 | Array size = 2*n-1 post-construcción | BAJA |
| 2 | `h_pow2` (buildTree) | 280 | n es potencia de 2 | BAJA |

**Naturaleza**: Invariantes de tamaño de array después de construcción bottom-up. Cerrables con aritmética y tracking de tamaño a través del foldl.

**Impacto**: Solo afecta `buildTree`. No afecta corrección criptográfica del Merkle tree.

### B. Sorry Comentados/Inactivos (13)

Todos dentro de bloques `/-...-/`. No compilan. No afectan `lake build`.

| Archivo | Cant. | Razón |
|---------|-------|-------|
| Verification/Theorems.lean | 7 | DEPRECATED — superseded por AlgebraicSemantics. Archivo entero comment-blocked (L32-L325). |
| Matrix/Perm.lean | 4 | Implementación incompleta de `inverse` + type coercion. Cada sorry en su propio `/-...-/` block. |
| NTT/Spec.lean | 1 | Hipótesis insuficientes (deprecated, en `/-...-/` block) |
| NTT/Properties.lean | 1 | Parseval incorrecto para campos finitos (en `/-...-/` block) |

### C. Axiomas Activos (12)

#### C.1. Goldilocks Field — 0 axiomas (ELIMINADOS)

**Estado**: Los 5 axiomas fundacionales fueron eliminados formalmente el 2026-02-11 (Bloque Central).

| Axioma | Estado | Estrategia |
|--------|--------|------------|
| `goldilocks_prime_is_prime` | THEOREM | Lucas primality + zpowMod |
| `goldilocks_canonical` | THEOREM | Subtype refactor (proof field `h_lt`) |
| `reduce128_correct` | THEOREM | Descomposición modular (6 sub-lemas) |
| `toZMod_pow` | THEOREM | Strong induction (Nat.strongRecOn) |
| `toZMod_inv` | THEOREM | Fermat (ZMod.pow_card_sub_one_eq_one) |

`grep "^axiom" AmoLean/Field/Goldilocks.lean` → **0 resultados**.

**Detalle completo**: `Bloque_central_plan.md`

#### C.2. BabyBear Field — 0 axiomas (ELIMINADOS)

**Estado**: Los 4 axiomas fundacionales fueron eliminados formalmente el 2026-02-12, aplicando la misma metodología del Bloque Central de Goldilocks.

| Axioma | Estado | Estrategia |
|--------|--------|------------|
| `babybear_prime_is_prime` | THEOREM | `native_decide` (31-bit, viable directamente) |
| `babybear_canonical` | THEOREM | Subtype refactor (proof field `h_lt`) |
| `toZMod_pow` | THEOREM | Strong induction (Nat.strongRecOn) |
| `toZMod_inv` | THEOREM | Fermat (ZMod.pow_card_sub_one_eq_one) |

Los 4 sorry de NTT/BabyBear.lean también fueron eliminados con `native_decide`.

`grep "^axiom" AmoLean/Field/BabyBear.lean` → **0 resultados**.
`grep "sorry" AmoLean/NTT/BabyBear.lean` → **0 resultados**.

#### C.3. NTT — 11 axiomas

**DAG de dependencias**:
```
Funciones opacas (interfaz):
  NTT_radix4 ──→ NTT_radix4_eq_spec ──→ roundtrip proofs
  INTT_radix4 ──→ INTT_radix4_NTT_radix4_identity

Propiedades:
  NTT_radix4_nil_axiom (edge case)
  butterfly4_orthogonality ──→ butterfly4 roundtrip
  ntt_spec_roundtrip ──→ roundtrip_any_algorithm
  intt_radix4_eq_spec_axiom ──→ algorithm equivalence

Bridge (List ↔ Finset):
  ct_recursive_eq_spec_axiom ──→ intt_recursive_eq_spec
  pow_pred_is_primitive ──→ inverse root properties
  inv_root_exp_equiv ──→ inverse root exponent
```

| # | Axioma | Archivo | Línea | Dificultad |
|---|--------|---------|-------|------------|
| 1 | `NTT_radix4` | Algorithm.lean | 38 | N/A (declaración opaca) |
| 2 | `NTT_radix4_eq_spec` | Algorithm.lean | 41 | MEDIA |
| 3 | `NTT_radix4_nil_axiom` | Algorithm.lean | 71 | BAJA |
| 4 | `INTT_radix4` | Algorithm.lean | 81 | N/A (declaración opaca) |
| 5 | `INTT_radix4_NTT_radix4_identity` | Algorithm.lean | 84 | MEDIA |
| 6 | `butterfly4_orthogonality` | Butterfly4.lean | 173 | MEDIA |
| 7 | `ntt_spec_roundtrip` | Equivalence.lean | 144 | ALTA |
| 8 | `intt_radix4_eq_spec_axiom` | Equivalence.lean | 154 | MEDIA |
| 9 | `ct_recursive_eq_spec_axiom` | ListFinsetBridge.lean | 103 | MEDIA (ya probado en Correctness.lean, ciclo de imports) |
| 10 | `pow_pred_is_primitive` | ListFinsetBridge.lean | 117 | MEDIA |
| 11 | `inv_root_exp_equiv` | ListFinsetBridge.lean | 130 | MEDIA |

**Impacto**: Fundamentan la cadena de verificación NTT. Sin estos axiomas, no hay prueba de que NTT_radix4 == NTT_spec == INTT roundtrip.

**Nota**: Axiomas #1 y #4 (`NTT_radix4`, `INTT_radix4`) son declaraciones opacas de funciones, no propiedades — su eliminación requiere implementar las funciones.

**Nota**: Axioma #9 (`ct_recursive_eq_spec_axiom`) ya está probado en `Correctness.lean` pero se necesita como axiom por ciclo de imports.

#### C.4. Matrix/Perm — 1 axioma

| # | Axioma | Línea | Dificultad |
|---|--------|-------|------------|
| 1 | `applyIndex_tensor_eq` | 636 | MUY ALTA — limitación del splitter de Lean para indexed inductives |

**Impacto**: Solo usado por `tensor_compose_pointwise`. Bajo impacto en el proyecto.

---

## Archivos del Proyecto

### Documentación Activa
```
TASKS_COMPLETED.md              ← ESTE ARCHIVO (fuente de verdad)
Bloque_central_plan.md          ← Plan + notas del Bloque Central (completado)
CONTEXT_RESUME.md               ← Resumen para reanudación de sesión
docs/
├── BENCHMARKS.md               ← Resultados de rendimiento
├── PRESENTATION_GUIDE.md       ← Guía de presentación del proyecto
├── README.md                   ← Índice de documentación
├── fase8_onda1_roadmap.md      ← Roadmap detallado de Onda 1 (completada)
├── project/
│   ├── DESIGN_DECISIONS.md     ← Decisiones de diseño activas (DD-001 a DD-024)
│   └── README.md               ← Descripción del proyecto
├── references/                 ← Material de referencia
└── archive/                    ← TODO lo obsoleto (~40 archivos)
    └── sorry_elimination_plan.md ← Plan AlgebraicSemantics (completado)
```

### Código Fuente Principal
```
AmoLean/
├── Field/
│   ├── Goldilocks.lean         ← Campo Goldilocks (0 axiomas, 0 sorry) ✓
│   └── BabyBear.lean           ← Campo BabyBear (0 axiomas, 0 sorry) ✓
├── NTT/
│   ├── Spec.lean               ← Especificación NTT (1 sorry inactivo)
│   ├── CooleyTukey.lean        ← Algoritmo recursivo
│   ├── Correctness.lean        ← Pruebas de corrección
│   ├── Properties.lean         ← Parseval (1 sorry inactivo)
│   ├── ListFinsetBridge.lean   ← Bridge List↔Finset (3 axiomas)
│   ├── BabyBear.lean           ← NTT para BabyBear (0 sorry) ✓
│   ├── Radix4/
│   │   ├── Algorithm.lean      ← NTT Radix-4 (5 axiomas)
│   │   ├── Butterfly4.lean     ← Butterfly4 (1 axioma)
│   │   └── Equivalence.lean    ← Equivalencia Radix4↔Spec (2 axiomas)
│   └── ...
├── Matrix/
│   └── Perm.lean               ← Permutaciones (1 axioma, 4 sorry inactivos)
├── Sigma/
│   ├── Basic.lean              ← Sigma-SPL DSL + lower
│   └── Expand.lean             ← Expansion a ScalarExprs
├── Verification/
│   ├── AlgebraicSemantics.lean ← PRINCIPAL: 0 sorry, 0 axiomas (~5700 líneas) ✓
│   ├── Semantics.lean          ← Semántica operacional
│   ├── Poseidon_Semantics.lean ← Poseidon2 (12 sorry — ADR-006)
│   └── Theorems.lean           ← DEPRECATED (7 sorry inactivos, archivo comment-blocked)
├── Backends/
│   └── Rust.lean               ← Generador de código Rust
├── FRI/
│   ├── Merkle.lean             ← Merkle tree (2 sorry)
│   └── ...
└── ...
```

---

## Métricas del Proyecto

| Métrica | Valor |
|---------|-------|
| Tests totales | 1550+ pass |
| Módulos compilando | 2647 |
| `lake build` | PASS (2026-02-12) |
| Speedup Lean→C (escalar) | 32.3x |
| AVX2 speedup | 4.00x |
| NTT throughput | 16-38 M elem/s |
| Optimization reduction | 91.67% |
| **Sorry activos** | **14** (12 Poseidon + 2 Merkle) |
| **Sorry inactivos** | **13** (comment-blocked, no compilan) |
| **Axiomas activos** | **12** (11 NTT + 1 Perm) |
| Sorry/axiomas en AlgebraicSemantics | **0 / 0** |
| Sorry/axiomas en Goldilocks | **0 / 0** |
| Sorry/axiomas en BabyBear | **0 / 0** |

---

## Trabajo Restante: Prioridades

### Prioridad 1: NTT axiomas (11) — BAJA VIABILIDAD (scope grande)

Requiere implementar funciones opacas (NTT_radix4, INTT_radix4) y probar propiedades algebraicas complejas (roundtrip, orthogonality). Trabajo significativo.

### Prioridad 2: Poseidon sorry (12) — BAJA VIABILIDAD (bloqueador técnico)

Bloqueados por limitación del match splitter de Lean 4 para indexed inductives. Puede requerir refactor arquitectural o workaround con `decide`/`native_decide`.

### Prioridad 3: Merkle sorry (2) + Perm axioma (1) — BAJA PRIORIDAD

Bajo impacto en el proyecto. Cerrables pero no urgentes.

---

*Creado: 2026-02-11*
*Actualizado: 2026-02-12 (BabyBear 4 axiomas + 4 sorry eliminados, conteos actualizados)*
