# AMO-Lean: Estado del Proyecto y Trabajo Completado

**Proyecto**: amo-lean (Automatic Mathematical Optimizer in Lean)
**Fecha**: 2026-02-12
**Versión actual**: post v1.0.1
**Lean**: 4.16.0, Mathlib v4.16.0
**Este es el documento canónico de estado del proyecto.** Cualquier otro roadmap o inventario está archivado en `docs/archive/`.

---

## Resumen Ejecutivo

AMO-Lean es un optimizador formal que transforma especificaciones matemáticas (MatExpr) en código C/Rust optimizado con corrección garantizada por construcción.

**Estado**: El teorema principal de correctness del lowering (`lowering_algebraic_correct`) está formalmente demostrado para todos los constructores de MatExpr relevantes, incluyendo el caso más difícil: Kronecker products (`lowering_kron_axiom` — 0 sorry, ALL 19/19 cases PROVEN). Los 5 axiomas fundacionales de Goldilocks Field fueron eliminados formalmente (Bloque Central, 2026-02-11). Los 4 axiomas de BabyBear Field + 4 sorry de NTT/BabyBear fueron eliminados (2026-02-12). Los 2 sorry de Merkle.lean fueron eliminados y los 13 sorry inactivos limpiados (2026-02-12).

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
| Merkle+Limpieza | 2 sorry Merkle + 13 sorry inactivos | COMPLETADA | 2026-02-12 |
| ListFinsetBridge | Eliminación 3 axiomas NTT (modular arith) | COMPLETADA | 2026-02-12 |

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
| **Sorry activos** | **12** | Poseidon(12) |
| **Sorry comentados (inactivos)** | **0** | Todos eliminados (2026-02-12) |
| **Axiomas activos** | **9** | NTT/Radix4(8), Perm(1) |

### A. Sorry Activos (12)

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

#### A.2. FRI/Merkle.lean — 0 sorry (COMPLETADO 2026-02-12)

**Estado**: Los 2 sorry fueron eliminados formalmente.

| # | Teorema | Estrategia | Estado |
|---|---------|-----------|--------|
| 1 | `h_size` (buildTree) | Helper `foldl_preserves_array_size` + `Array.size_mkArray` + `simp [Array.set!]` | THEOREM |
| 2 | `h_pow2` (buildTree) | Refactor: `if h : 2^(Nat.log2 n) = n` captura hypothesis directamente | THEOREM |

**Lecciones aprendidas**:
- `h_size`: La clave fue un lemma genérico `foldl_preserves_array_size` que prueba que foldl preserva tamaño de array cuando cada paso lo hace. `simp [Array.set!]` cierra automáticamente que `set!` preserva tamaño.
- `h_pow2`: En lugar de probar que `n &&& (n-1) = 0` implica potencia de 2 (requiere bitwise theory), se cambió la condición a `2^(Nat.log2 n) = n` que es decidable y captura la hypothesis directamente con `dite`.

### B. Sorry Comentados/Inactivos — 0 (LIMPIADOS 2026-02-12)

Todos los 13 sorry inactivos fueron eliminados:

| Archivo | Cant. eliminados | Acción |
|---------|-----------------|--------|
| Verification/Theorems.lean | 7 | Reemplazado por stub (archivo deprecated, superseded por AlgebraicSemantics) |
| Matrix/Perm.lean | 4 | Borrados 4 bloques `/-...-/` (inverse_inverse, inverse_compose, tensor_identity_left/right) |
| NTT/Spec.lean | 1 | Borrado bloque `/-...-/` (ntt_intt_identity_deprecated, hipótesis insuficientes) |
| NTT/Properties.lean | 1 | Borrado bloque `/-...-/` (parseval, incorrecto para campos finitos) |

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

#### C.3. NTT — 8 axiomas (was 11, -3 ListFinsetBridge)

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

**Impacto**: Fundamentan la cadena de verificación NTT Radix-4. Sin estos axiomas, no hay prueba de que NTT_radix4 == NTT_spec == INTT roundtrip. La cadena Radix-2 (Cooley-Tukey) ya está 100% probada sin axiomas.

**Nota**: Axiomas #1 y #4 (`NTT_radix4`, `INTT_radix4`) son declaraciones opacas de funciones, no propiedades — su eliminación requiere implementar las funciones.

#### C.3b. NTT ListFinsetBridge — 0 axiomas (ELIMINADOS 2026-02-12)

3 axiomas eliminados moviendo `intt_recursive_eq_spec` y sus dependencias de ListFinsetBridge.lean a Correctness.lean:

| Axioma | Estado | Estrategia |
|--------|--------|------------|
| `ct_recursive_eq_spec_axiom` | THEOREM | Reemplazado por referencia directa a `ct_recursive_eq_spec` (probado en mismo archivo) |
| `pow_pred_is_primitive` | THEOREM | Aritmética modular: `pred_mul_mod` demuestra `(n-1)*k % n = n-k`, luego `ω^(n-k) ≠ 1` por primitividad |
| `inv_root_exp_equiv` | THEOREM | Generalización: `pred_mul_mod_general` demuestra `(n-1)*m % n = (n - m%n) % n` |

`grep "^axiom" AmoLean/NTT/ListFinsetBridge.lean` → **0 resultados**.

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
│   ├── Spec.lean               ← Especificación NTT (0 sorry) ✓
│   ├── CooleyTukey.lean        ← Algoritmo recursivo
│   ├── Correctness.lean        ← Pruebas de corrección
│   ├── Properties.lean         ← Parseval (0 sorry) ✓
│   ├── ListFinsetBridge.lean   ← Bridge List↔Finset (0 axiomas) ✓
│   ├── BabyBear.lean           ← NTT para BabyBear (0 sorry) ✓
│   ├── Radix4/
│   │   ├── Algorithm.lean      ← NTT Radix-4 (5 axiomas)
│   │   ├── Butterfly4.lean     ← Butterfly4 (1 axioma)
│   │   └── Equivalence.lean    ← Equivalencia Radix4↔Spec (2 axiomas)
│   └── ...
├── Matrix/
│   └── Perm.lean               ← Permutaciones (1 axioma, 0 sorry) ✓
├── Sigma/
│   ├── Basic.lean              ← Sigma-SPL DSL + lower
│   └── Expand.lean             ← Expansion a ScalarExprs
├── Verification/
│   ├── AlgebraicSemantics.lean ← PRINCIPAL: 0 sorry, 0 axiomas (~5700 líneas) ✓
│   ├── Semantics.lean          ← Semántica operacional
│   ├── Poseidon_Semantics.lean ← Poseidon2 (12 sorry — ADR-006)
│   └── Theorems.lean           ← DEPRECATED (stub, 0 sorry) ✓
├── Backends/
│   └── Rust.lean               ← Generador de código Rust
├── FRI/
│   ├── Merkle.lean             ← Merkle tree (0 sorry, 0 axiomas) ✓
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
| **Sorry activos** | **12** (12 Poseidon) |
| **Sorry inactivos** | **0** (todos eliminados) |
| **Axiomas activos** | **9** (8 NTT/Radix4 + 1 Perm) |
| Sorry/axiomas en AlgebraicSemantics | **0 / 0** |
| Sorry/axiomas en Goldilocks | **0 / 0** |
| Sorry/axiomas en BabyBear | **0 / 0** |
| Sorry/axiomas en FRI/Merkle | **0 / 0** |

---

## Trabajo Restante: Prioridades

### Prioridad 1: Poseidon sorry (12) — VIABILIDAD MEDIA-BAJA (bloqueador técnico)

Bloqueados por limitación del match splitter de Lean 4 para indexed inductives. Todos verificados computacionalmente (21 tests, 100%). Tres posibles vías:

1. **Workaround `native_decide`**: No viable (n simbólico, no concreto)
2. **Refactor a constructores más simples**: Evitar pattern matching profundo en `evalMatExpr`. Viable pero requiere ~2 sesiones de refactor.
3. **Esperar mejoras en Lean**: El splitter de Lean 4 sigue mejorando. Lean 4.17+ podría resolver.

**Impacto**: Aislado. Solo afecta verificación end-to-end de Poseidon2. No bloquea NTT, FRI, ni el pipeline principal.

### Prioridad 2: NTT/Radix4 axiomas (8) — VIABILIDAD MEDIA (scope segmentable)

Los 8 axiomas restantes (todos en NTT/Radix4/) se dividen en 2 categorías:

**Categoría A — Requieren álgebra DFT (5 axiomas, MEDIA-ALTA dificultad)**:
- `NTT_radix4_eq_spec`: Inducción sobre recurrencia radix-4 → spec.
- `INTT_radix4_NTT_radix4_identity`: Ortogonalidad DFT (ya probada para Finset).
- `butterfly4_orthogonality`: Álgebra matricial 4×4 (Vandermonde).
- `ntt_spec_roundtrip`: Roundtrip spec-based (duplica Finset proof existente).
- `intt_radix4_eq_spec_axiom`: Derivable de otros axiomas.

**Categoría B — Fundamentales/Opacas (3 axiomas, N/A)**:
- `NTT_radix4`: Declaración opaca de función. Requiere implementación concreta.
- `INTT_radix4`: Declaración opaca de función. Requiere implementación concreta.
- `NTT_radix4_nil_axiom`: Edge case (borde vacío). Impacto mínimo.

**Impacto**: Los axiomas fundamentan la cadena Radix-4. La cadena Radix-2 (Cooley-Tukey) ya está 100% probada formalmente en `Correctness.lean` sin axiomas, incluyendo INTT roundtrip.

### Prioridad 3: Perm axioma (1) — MUY BAJA PRIORIDAD

`applyIndex_tensor_eq`: Limitación fundamental del splitter de Lean 4 para indexed inductives. Bajo impacto (solo usado por `tensor_compose_pointwise`). No hay workaround conocido.

---

*Creado: 2026-02-11*
*Actualizado: 2026-02-12 (ListFinsetBridge 3 axiomas eliminados: 12→9 axiomas globales)*
