# Contexto de Reanudación: Fase 8 Onda 1 — COMPLETADA

**Fecha**: 2026-02-11
**Archivo principal**: `AmoLean/Verification/AlgebraicSemantics.lean` (~5700 líneas)
**Lean**: 4.16.0, Mathlib v4.16.0

## Objetivo

~~Cerrar los sorry residuales en `AlgebraicSemantics.lean`. Reducir sorry-using declarations a 0.~~

**COMPLETADO**: `lowering_kron_axiom` tiene 0 sorry. ALL 19/19 cases PROVEN.

## Estado Actual del Build

```
0 ERRORES de compilación ✓
0 sorry-using declarations en AlgebraicSemantics.lean ✓
lowering_kron_axiom: PROVEN (0 sorry)
```

## Sorry Inventory — CERRADO

| # | Caso | Estado |
|---|------|--------|
| 1 | A⊗I non-zero (stride scatter assembly) | ✓ CERRADO (sesión S-6) |
| 2 | A⊗I zero (mirror of I⊗B zero) | ✓ CERRADO (sesión S-6) |

## Trabajo Completado (todas las sesiones)

### S-1: Termination proof
- Convertido de `match mat` + WF recursion a `induction mat generalizing`

### S-2: lower_preserves_size_ge + Bug fix
- Añadidos `evalScatter_block/stride_preserves_wm_size`
- Fix: Bug semántico en `evalSigmaAlg` loop (readMem overwrite)

### S-3: WriteMem irrelevance
- `evalSigmaAlg_writeMem_irrelevant` para TODOS los constructores incl. kron

### S-4: Reestructuración + I⊗B case
- Reestructuración de signatura con `ihA`, `ihB`
- Lemas auxiliares de Gather (block + stride)
- I⊗B completo: non-zero (~95 líneas) + zero (~70 líneas)

### S-5: A⊗I infraestructura
- `stride_scatter_loop_inv` + helpers
- `hker`, `hvals_len`, `hvals_eq`, `hinv` — toda la infraestructura

### S-6: A⊗I assembly + zero + A⊗B — FINAL
- **A⊗I non-zero assembly** (~45 líneas): Pointwise equality via `List.ext_getElem`,
  bridging `getD` ↔ `getElem` via `get?_eq_getElem?` + `getElem?_eq_getElem` + `getD_some`.
  Key insight: `congrArg` para pattern match failures, `Option.some.injEq` para inyectividad.
- **A⊗I zero** (~55 líneas): Mirror of I⊗B zero case. `lower a = .nop` → loop = zeros,
  `evalMatExprAlg` kron A⊗I branch with zero a = replicate 0.
- **A⊗B unreachable**: `exfalso` — trivial via contradiction on `isIdentity` flags.

## Progreso Global

| Sesión | Sorry eliminados | Sorry restantes | Hallazgos clave |
|--------|-----------------|-----------------|-----------------|
| S-1 | P1 (termination) | 4 | `induction mat generalizing` resuelve WF |
| S-2 | P2 (2 sorry) + loop fix | 2 | Bug semántico en evalSigmaAlg loop |
| S-3 | P3 (kron wm irrelevance) | **1 declaration** | `simp only [wrapper_lemma]` |
| S-4 | I⊗B completo | **1 decl (2 sorry)** | Block scatter pattern end-to-end |
| S-5 | A⊗I infra complete | **1 decl (2 sorry)** | Stride infra works |
| S-6 | **A⊗I + A⊗B** | **0 sorry** | `congrArg`, Option-level proofs |

## Fase 8 Onda 1 — Estado Final

Todos los 5 entregables completados:
- [x] E3: Sorry cleanup (Theorems.lean deprecated)
- [x] A1: BabyBear field + NTTField instance + oracle tests
- [x] A2: Rust codegen backend (expandedSigmaToRust)
- [x] B1: Radix-4 butterfly4 C codegen
- [x] C1: lowering_kron_axiom PROVEN — ALL 19/19 cases, 0 sorry

## Lecciones Clave (L-176 a L-181)

- **L-176**: `congrArg (fun l => f l) h.symm` como alternativa a `rw` cuando simp transforma el pattern
- **L-177**: Trabajar a nivel `getElem?` (Option) evita "motive not type correct" con dependent types
- **L-178**: Cadena `getD` ↔ `getElem`: `get?_eq_getElem?` + `getElem?_eq_getElem` + `getD_some`
- **L-179**: `Nat.mul_div_cancel` (a*b/b=a) vs `Nat.mul_div_cancel_left` (b*a/b=a) — order matters
- **L-180**: `simp only [Option.some.injEq] at h` para inyectividad robusta (mejor que `▸`)
- **L-181**: `adjustStride .nop = .nop` es definitionally true — no necesita lema explícito

## Archivos Clave

- `AmoLean/Verification/AlgebraicSemantics.lean` — archivo principal (~5700 líneas)
- `AmoLean/Verification/Semantics.lean` — `evalSigma` (operational semantics)
- `AmoLean/Sigma/Basic.lean` — `lower`, `adjustBlock`, `adjustStride`
- `AmoLean/Matrix/Basic.lean` — `MatExpr`, `nodeCount`
- `docs/fase8_onda1_roadmap.md` — roadmap completo de Onda 1
