# AMO-Lean: Estado del Proyecto y Trabajo Completado

**Proyecto**: amo-lean (Automatic Mathematical Optimizer in Lean)
**Fecha**: 2026-02-11
**Versión actual**: post v1.0.1
**Lean**: 4.16.0, Mathlib v4.16.0
**Este es el documento canónico de estado del proyecto.** Cualquier otro roadmap o inventario está archivado en `docs/archive/`.

---

## Resumen Ejecutivo

AMO-Lean es un optimizador formal que transforma especificaciones matemáticas (MatExpr) en código C/Rust optimizado con corrección garantizada por construcción.

**Estado**: El teorema principal de correctness del lowering (`lowering_algebraic_correct`) está formalmente demostrado para todos los constructores de MatExpr relevantes, incluyendo el caso más difícil: Kronecker products (`lowering_kron_axiom` — 0 sorry, ALL 19/19 cases PROVEN).

---

## Fases Completadas (0-5 + 8 Onda 1)

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

### Fase 8 Onda 1: Detalle de Entregables

| ID | Entregable | Descripción | Estado |
|----|-----------|-------------|--------|
| E3 | Sorry cleanup | Theorems.lean deprecated (7 sorry inactivos) | COMPLETADO |
| A1 | BabyBear field | Campo BabyBear (p=2013265921) + NTTField instance | COMPLETADO |
| A2 | Rust codegen | expandedSigmaToRust genera código Rust compilable | COMPLETADO |
| B1 | Radix-4 codegen | butterfly4 kernel integrado en pipeline C | COMPLETADO |
| C1 | Kron verification | lowering_kron_axiom PROVEN — 0 sorry | COMPLETADO |

---

## Trabajo de la Última Sesión (S-6, 2026-02-11)

### Objetivo
Cerrar los 2 últimos sorry en `lowering_kron_axiom` (AlgebraicSemantics.lean).

### Resultados
- **A⊗I non-zero assembly** (~45 líneas, 8 iteraciones compile-fix):
  - Pointwise equality via `List.ext_getElem`
  - Bridge `getD` ↔ `getElem` via cadena: `get?_eq_getElem?` + `getElem?_eq_getElem` + `getD_some`
  - `congrArg` para pattern match failures donde `rw` falla post-simp
  - `Option.some.injEq` via simp para inyectividad robusta

- **A⊗I zero case** (~55 líneas, compiló al primer intento):
  - Mirror del zero B case (I⊗B branch)
  - `lower a = .nop` → loop = zeros, `evalMatExprAlg` kron A⊗I = replicate 0

- **A⊗B unreachable**: `exfalso` — trivial via contradicción en flags `isIdentity`

### Verificación
```
lake build: PASS
AlgebraicSemantics.lean: 0 sorry, 0 axiomas
lowering_kron_axiom: ALL 19/19 cases PROVEN
```

### Lecciones Aprendidas (L-176 a L-181)
- **L-176**: `congrArg (fun l => f l) h.symm` como alternativa a `rw` cuando simp transforma el pattern
- **L-177**: Trabajar a nivel `getElem?` (Option) evita "motive not type correct" con dependent types
- **L-178**: Cadena `getD` ↔ `getElem`: `get?_eq_getElem?` + `getElem?_eq_getElem` + `getD_some`
- **L-179**: `Nat.mul_div_cancel` (a*b/b=a) vs `Nat.mul_div_cancel_left` (b*a/b=a) — order matters
- **L-180**: `simp only [Option.some.injEq] at h` para inyectividad robusta (mejor que `▸`)
- **L-181**: `adjustStride .nop = .nop` es definitionally true — no necesita lema explícito

### Commit
`891a298` — `feat(verification): lowering_kron_axiom PROVEN — 0 sorry, ALL 19/19 cases`

---

## Inventario Completo de Sorry y Axiomas

### Resumen Cuantitativo

| Categoría | Cantidad | Archivos |
|-----------|----------|----------|
| **Sorry activos** | 18 | Poseidon(12), BabyBear(4), Merkle(2) |
| **Sorry comentados (inactivos)** | 6 | Theorems(7†), Perm(4), Spec(1), Properties(1) |
| **Axiomas activos** | 17 | NTT(11), Goldilocks(5), Perm(1) |

†Los 7 de Theorems.lean están dentro de un comment-block `/-...-/`.

### A. Sorry Activos (18)

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

#### A.2. NTT/BabyBear.lean — 4 sorry (computational verification)

| # | Teorema | Línea | Descripción | Dificultad |
|---|---------|-------|-------------|------------|
| 1-3 | `babybear_generator_is_primitive_root` | 96 | g^((p-1)/q) ≠ 1 para q=2,3,5 | BAJA (native_decide timeout) |
| 4 | `babybear_generator_order` | 103 | g^(p-1) = 1 (Fermat) | BAJA (native_decide timeout) |

**Naturaleza**: Hechos computacionales puros. `native_decide` podría resolverlos pero timeout por exponentes grandes (p=2013265921). Verificados por #eval tests en el mismo archivo.

**Impacto**: Solo afecta la instancia NTTField de BabyBear. No afecta Goldilocks ni AlgebraicSemantics.

#### A.3. FRI/Merkle.lean — 2 sorry (size invariants)

| # | Teorema | Línea | Descripción | Dificultad |
|---|---------|-------|-------------|------------|
| 1 | `h_size` (buildTree) | 279 | Array size = 2*n-1 post-construcción | BAJA |
| 2 | `h_pow2` (buildTree) | 280 | n es potencia de 2 | BAJA |

**Naturaleza**: Invariantes de tamaño de array después de construcción bottom-up. Cerrables con aritmética y tracking de tamaño a través del foldl.

**Impacto**: Solo afecta `buildTree`. No afecta corrección criptográfica del Merkle tree.

### B. Sorry Comentados/Inactivos (6+7)

Todos dentro de bloques `/-...-/`. No compilan. No afectan el proyecto.

| Archivo | Cant. | Razón |
|---------|-------|-------|
| Verification/Theorems.lean | 7 | DEPRECATED — superseded por AlgebraicSemantics |
| Matrix/Perm.lean | 4 | Implementación incompleta de `inverse` + type coercion |
| NTT/Spec.lean | 1 | Hipótesis insuficientes (deprecated) |
| NTT/Properties.lean | 1 | Parseval incorrecto para campos finitos |

### C. Axiomas Activos (17)

#### C.1. Goldilocks Field — 5 axiomas

**DAG de dependencias**:
```
goldilocks_prime_is_prime ──→ Fact instance ──→ ZMod instance ──→ Field instance
                         └──→ goldilocks_canonical ──→ todas las operaciones
reduce128_correct ──→ mul_val_eq ──→ toZMod_mul
toZMod_pow ──→ npow_succ, zpow_succ'
toZMod_inv ──→ mul_inv_cancel ──→ Field instance
```

| # | Axioma | Línea | Dificultad de eliminación |
|---|--------|-------|--------------------------|
| 1 | `goldilocks_prime_is_prime` | 45 | MUY ALTA — p demasiado grande para `decide`/`native_decide` |
| 2 | `goldilocks_canonical` | 319 | MEDIA — probar por caso para cada operación |
| 3 | `reduce128_correct` | 539 | ALTA — aritmética modular 128-bit con split cases |
| 4 | `toZMod_pow` | 765 | MEDIA — inducción sobre binary exponentiation |
| 5 | `toZMod_inv` | 781 | MEDIA — depende de toZMod_pow + Fermat |

**Impacto**: CRÍTICO. Fundamentan CommRing + Field instance de GoldilocksField. Todos los teoremas que usan aritmética de campo dependen transitivamente de estos.

#### C.2. NTT — 11 axiomas

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
| 1 | `NTT_radix4` | Algorithm.lean | 38 | N/A (declaración) |
| 2 | `NTT_radix4_eq_spec` | Algorithm.lean | 41 | MEDIA |
| 3 | `NTT_radix4_nil_axiom` | Algorithm.lean | 71 | BAJA |
| 4 | `INTT_radix4` | Algorithm.lean | 81 | N/A (declaración) |
| 5 | `INTT_radix4_NTT_radix4_identity` | Algorithm.lean | 84 | MEDIA |
| 6 | `butterfly4_orthogonality` | Butterfly4.lean | 173 | MEDIA |
| 7 | `ntt_spec_roundtrip` | Equivalence.lean | 144 | ALTA |
| 8 | `intt_radix4_eq_spec_axiom` | Equivalence.lean | 154 | MEDIA |
| 9 | `ct_recursive_eq_spec_axiom` | ListFinsetBridge.lean | 103 | MEDIA (ya probado, ciclo de imports) |
| 10 | `pow_pred_is_primitive` | ListFinsetBridge.lean | 117 | MEDIA |
| 11 | `inv_root_exp_equiv` | ListFinsetBridge.lean | 130 | MEDIA |

**Impacto**: Fundamentan la cadena de verificación NTT. Sin estos axiomas, no hay prueba de que NTT_radix4 == NTT_spec == INTT roundtrip.

**Nota**: Axioma #9 (`ct_recursive_eq_spec_axiom`) ya está probado en `Correctness.lean` pero se necesita como axiom por ciclo de imports.

#### C.3. Matrix/Perm — 1 axioma

| # | Axioma | Línea | Dificultad |
|---|--------|-------|------------|
| 1 | `applyIndex_tensor_eq` | 636 | MUY ALTA — limitación del splitter de Lean para indexed inductives |

**Impacto**: Solo usado por `tensor_compose_pointwise`. Bajo impacto en el proyecto.

---

## Archivos del Proyecto

### Documentación Activa
```
TASKS_COMPLETED.md              ← ESTE ARCHIVO (fuente de verdad)
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
```

### Código Fuente Principal
```
AmoLean/
├── Field/
│   ├── Goldilocks.lean         ← Campo Goldilocks (5 axiomas)
│   └── BabyBear.lean           ← Campo BabyBear (4 sorry computacionales)
├── NTT/
│   ├── Spec.lean               ← Especificación NTT
│   ├── CooleyTukey.lean        ← Algoritmo recursivo
│   ├── Correctness.lean        ← Pruebas de corrección
│   ├── ListFinsetBridge.lean   ← Bridge List↔Finset (3 axiomas)
│   ├── BabyBear.lean           ← NTT para BabyBear
│   ├── Radix4/
│   │   ├── Algorithm.lean      ← NTT Radix-4 (5 axiomas)
│   │   ├── Butterfly4.lean     ← Butterfly4 (1 axioma)
│   │   └── Equivalence.lean    ← Equivalencia Radix4↔Spec (2 axiomas)
│   └── ...
├── Matrix/
│   └── Perm.lean               ← Permutaciones (1 axioma, 4 sorry comentados)
├── Sigma/
│   ├── Basic.lean              ← Sigma-SPL DSL + lower
│   └── Expand.lean             ← Expansion a ScalarExprs
├── Verification/
│   ├── AlgebraicSemantics.lean ← PRINCIPAL: 0 sorry, 0 axiomas (~5700 líneas)
│   ├── Semantics.lean          ← Semántica operacional
│   ├── Poseidon_Semantics.lean ← Poseidon2 (12 sorry — ADR-006)
│   └── Theorems.lean           ← DEPRECATED (7 sorry comentados)
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
| Módulos compilando | 2646 |
| Speedup Lean→C (escalar) | 32.3x |
| AVX2 speedup | 4.00x |
| NTT throughput | 16-38 M elem/s |
| Optimization reduction | 91.67% |
| Sorry activos | 18 (12 Poseidon + 4 BabyBear + 2 Merkle) |
| Axiomas activos | 17 (5 Goldilocks + 11 NTT + 1 Perm) |
| Sorry/axiomas en AlgebraicSemantics | **0 / 0** |

---

*Creado: 2026-02-11*
*Próxima actualización: al iniciar nueva fase de trabajo*
