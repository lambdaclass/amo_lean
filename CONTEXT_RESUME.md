# Contexto de Reanudación: Fase 8 Onda 1 C1 Capa 2 Residuales

**Fecha**: 2026-02-11
**Archivo principal**: `AmoLean/Verification/AlgebraicSemantics.lean` (~5625 líneas)
**Lean**: 4.16.0, Mathlib v4.16.0

## Objetivo

Cerrar los sorry residuales en `AlgebraicSemantics.lean`. Reducir sorry-using declarations a 0.

## Estado Actual del Build

```
0 ERRORES de compilación ✓

1 sorry-using declaration:
  - lowering_kron_axiom (línea 5183) — 2 sorry:
    1. Línea 5422: A⊗I non-zero case (assembly/pointwise proof)
    2. Línea 5424: A⊗I zero case
```

## Sorry Inventory (2 sorry restantes, todos en lowering_kron_axiom)

| # | Caso | Línea | Descripción | Infraestructura |
|---|------|-------|-------------|-----------------|
| 1 | A⊗I non-zero | 5422 | Pointwise equality: stride scatter result = evalMatExprAlg A⊗I format | h_lf, hker, hvals_len, hvals_eq, hinv — TODO proven |
| 2 | A⊗I zero | 5424 | Both sides = replicate (m₁*m₂) default when ¬HasNoZero a | Simétrico al zero B case (I⊗B, lines 5295-5362) |

## Trabajo Completado

### P1: Termination proof ✅ (sesiones anteriores)
- Convertido de `match mat` + WF recursion a `induction mat generalizing`
- Eliminó el bloqueador PSigma packing

### P2: lower_preserves_size_ge kron I⊗B y A⊗I ✅ (sesiones anteriores)
- Añadidos `evalScatter_block_preserves_wm_size` y `evalScatter_stride_preserves_wm_size`
- Gen theorems cambiados de `hwm : = m₁ * blockSize` a `hwm : ≥ m₁ * blockSize`, retornan `= st.writeMem.size`
- Sorry en I⊗B y A⊗I cerrados usando `evalSigmaAlg_loop_preserves_wm_size_with_bound` + gen theorems
- Fix: explicit type annotation en `have hst1` para omega, `rename_i` para variables inaccessibles, `simp [freshLoopVar]` para hv_fresh

### DESCUBRIMIENTO CRÍTICO: Bug en semántica de loop de evalSigmaAlg ✅ FIXED (sesiones anteriores)
- **Problema**: `evalSigmaAlg` (algebraic, usada en pruebas) tenía semántica de loop DIFERENTE a `evalSigma` (operational, usada en tests)
- **evalSigma** (correcto): `foldl (fun st i => evalSigma env' st body) state` — pasa output del body directamente
- **evalSigmaAlg** (incorrecto): `foldl (fun st i => let st' = eval body; {readMem := st'.writeMem, writeMem := st'.writeMem}) state` — sobreescribía readMem con writeMem
- **Fix**: Una línea cambiada en `evalSigmaAlg` loop case (línea ~970). Todos los proofs existentes compilan sin cambios.

### P3: evalSigmaAlg_writeMem_irrelevant kron case ✅ CERRADO (sesión S-3)

**Problema**: Demostrar que `evalSigmaAlg` con dos writeMem distintos produce el mismo resultado para el caso kron.

### P4: lowering_kron_axiom — Reestructuración + I⊗B case ✅ (sesión S-4)

**Completado**:
1. **Reestructuración de signatura** (Paso 1-2 del plan):
   - Añadidos parámetros `hwf : IsWellFormedNTT (.kron a b)`, `ihA`, `ihB` a `lowering_kron_axiom`
   - Updated call site en `lowering_algebraic_correct` (línea 5526) pasando IH recursivamente
   - `subst ha_sq; subst hb_sq` para unificar m₁=n₁, m₂=n₂

2. **Lemas auxiliares de Gather** (Paso 3-4):
   - `evalGather_block_ofList_eq_drop_take` (línea ~1777): block gather = drop/take
   - `evalGather_stride_ofList_eq_lane` (línea ~1897): stride gather = map getD con stride pattern
   - `read_ofList_eq_getD` (línea 85): Memory.read ∘ ofList = getD

3. **Caso I⊗B completo** (Paso 6) — ~160 líneas:
   - **Non-zero B sub-case** (lines 5200-5293): Block scatter + kernel correctness via ihB
     - `lower_hasNoSeqLower_contiguous` → `hk` (lower b = .compute k contiguous contiguous)
     - `lower_hasNoSeqLower_state_eq` → `hs` (state independence)
     - `h_lf` : lowerFresh(.kron a b) = .loop m₁ 0 (.compute k (block gather) (block scatter))
     - `hker`: evalKernelAlg k (block_i) = evalMatExprAlg b (block_i) via ihB chain
     - `hvals_len`, `hvals_eq`: length + value correctness per block
     - `hinv`: block_scatter_loop_inv da toList = flatMap vals ++ drop
     - Final: `rfl`-based proof after rewriting both sides
   - **Zero B sub-case** (lines 5295-5362):
     - `lower_hasNoSeqLower_notHasNoZero_is_nop` → lower b = .nop
     - LHS: loop over .nop = zeros (induction on List.range m₁)
     - RHS: evalMatExprAlg of zero matrix = replicate default (induction on flatMap)
     - Fixed: `simp only [...] at ih ⊢` pattern for foldl_cons, `Nat.min_def` + `split_ifs` for min

### P4 (cont): A⊗I case — Infraestructura DONE, Assembly PENDING (sesión S-5, actual)

**Completado** (A⊗I non-zero setup, lines 5370-5416):
- `hk`, `hs`, `hk'`: lower a = .compute k contiguous contiguous (con state independence)
- `h_lf`: lowerFresh(.kron a b) = .loop m₂ 0 (.compute k (stride gather) (stride scatter))
- `hker`: ∀ w, w.length = m₁ → evalKernelAlg k w = evalMatExprAlg a w (via ihA chain)
- `hvals_len`: ∀ j < m₂, (vals j).length = m₁
- `hvals_eq`: ∀ j < m₂, vals j = evalMatExprAlg a (lane j of v)
- `hinv`: stride_scatter_loop_inv m₁ m₂ (Memory.zeros (m₁*m₂)) vals...

**Pendiente** (2 sorry):
1. **Assembly del non-zero A⊗I case** (línea 5422):
   - Infraestructura completa arriba — falta conectar con evalMatExprAlg RHS
   - Estrategia: `rw [h_lf]` → unfold runSigmaAlg → use `hinv` for LHS pointwise → unfold evalMatExprAlg for RHS → connect via `hvals_eq`
   - **Dificultad principal**: `rw [hvals_eq]` inside a `getElem` causes "motive not type correct" (dependent types). Solución: trabajar a nivel `?` (Option) con `getElem?` en vez de `getElem`.
   - **Otra dificultad**: Simplificar `match processedLanes[n%m₂]? with | some ld => ld.getD ... | none => default` requiere probar que `processedLanes[n%m₂]? = some (evalMatExprAlg a (lane n%m₂))` y luego simplificar `getD` → `getElem` cuando el índice está en bounds.

2. **Zero A case** (línea 5424):
   - Simétrico al zero B case del I⊗B branch (lines 5295-5362)
   - Patrón: lower a = .nop → loop over .nop = zeros, evalMatExprAlg of zero = replicate default
   - Estimación: ~50-70 líneas, dificultad MEDIA (adaptar pattern de zero B)

**Paso 8 (pendiente)**: A⊗B unreachable — trivial (~3 líneas), se posterga hasta cerrar A⊗I.

## Errores Encontrados y Soluciones (Sesión S-5)

### Error 1: `simp only [...] at ih ⊢` pattern (I⊗B zero case, línea 5325)
- **Problema**: `simp only [List.foldl_cons, evalSigmaAlg]` simplificaba el goal pero no `ih`, causando type mismatch en `exact ih st`
- **Solución**: Añadir `at ih ⊢` → `simp only [List.foldl_cons, evalSigmaAlg] at ih ⊢; exact ih st`

### Error 2: `symm; apply Nat.min_eq_left` (I⊗B zero case, línea 5357)
- **Problema**: `symm` swapped la ecuación a dirección incorrecta para `Nat.min_eq_left`
- **Solución**: `rw [Nat.min_def]; split_ifs with hle` → `· rfl` + omega fallback

### Error 3: `cases a.isIdentity <;> simp_all` crashes (A⊗I, ha_false)
- **Problema**: `simp_all` intentaba unfold `isIdentity` match, causando "failed to generate splitter for match"
- **Solución**: Usar `match h : a.isIdentity with | true => exact absurd h h_id_a | false => rfl`

### Error 4: Bool if-then-else no reduce (A⊗I, h_lf)
- **Problema**: `simp only [ha_false, h_id_b, ...]` no reducía `if false then ... else ...`
- **Solución**: Añadir `Bool.false_eq_true, ite_false, ite_true` al simp set

### Error 5: `rw [hvals_eq]` motive not type correct (A⊗I pointwise)
- **Problema**: Rewriting `vals (n%m₂)` inside `(vals (n%m₂))[n/m₂]` (getElem) falla porque el proof `h_in_bounds` depende de `vals`
- **Solución pendiente**: Trabajar a nivel `?` (Option) — `rw [hvals_eq]` en `(vals (n%m₂))[n/m₂]?` funciona sin problemas de dependent types
- **Alternativa**: Usar `conv` para target the exact subexpression, o `congr 1` + `exact hvals_eq`

### Error 6: `h_wm_len ▸ m₁ * m₂ ≤ n` invalid ▸ (A⊗I, n≥m₁*m₂)
- **Problema**: `▸` notation inside `by omega` can't cast between non-matching types
- **Solución**: Usar `apply List.getElem?_eq_none; unfold Memory.toList Memory.size at *; rw [Array.length_toList]; omega`

## Tareas Pendientes (para reanudar)

### Tarea 1: Cerrar sorry A⊗I non-zero (línea 5422, prioridad ALTA)
**Estrategia recomendada**:
```lean
-- Después de h_lf, hker, hvals_len, hvals_eq, hinv ya probados:
rw [h_lf]
simp only [runSigmaAlg, EvalState.init, evalSigmaAlg.eq_2,
            compute_loop_decompose_writeMem, evalScatter_stride_var_eq]
-- Eliminar take (size = m₁*m₂)
-- apply List.ext_getElem?, intro n
-- by_cases hn : n < m₁ * m₂
-- En la rama n < m₁*m₂:
--   rw [hp_inv]  -- LHS = (vals (n%m₂))[n/m₂]?
--   rw [hvals_eq (n%m₂) hp_mod]  -- SEGURO a nivel ?
--   -- RHS: simp [List.getElem?_map, List.getElem?_range, hn, Option.map_some']
--   -- Simplificar match processedLanes[n%m₂]? → some (evalMatExprAlg a (lane))
--   -- Conectar getD con getElem? via List.getD = (l[n]?).getD d
```

### Tarea 2: Cerrar sorry A⊗I zero (línea 5424, prioridad MEDIA)
**Estrategia**: Adaptar pattern de zero B case (líneas 5295-5362)
- `lower_hasNoSeqLower_notHasNoZero_is_nop a h_nsl_a` → lower a = .nop
- LHS: loop over .nop = zeros
- RHS: evalMatExprAlg of A⊗I where a is zero → replicate default
- Estimación: ~50-70 líneas

### Tarea 3: Paso 8 — A⊗B unreachable (línea ~5425 después de cerrar T1/T2)
**Estrategia**: `exfalso; exact h_id.elim ...` — trivial (~3 líneas)
- Reutiliza pattern de P3 (kron writeMem irrelevance)

### Tarea 4: Verificación final
- `lake build` limpio (0 sorry, 0 errors)
- Actualizar comment block en línea 5432 (status)
- Commit final

## Archivos Clave de Referencia

- `AmoLean/Verification/AlgebraicSemantics.lean` — archivo principal (~5625 líneas)
- `AmoLean/Verification/Semantics.lean` — `evalSigma` (operational, referencia correcta para loop semantics)
- `AmoLean/Sigma/Basic.lean` — `lower`, `adjustBlock`, `adjustStride`, `freshLoopVar`
- `AmoLean/Matrix/Basic.lean` — `MatExpr`, `nodeCount`

### Definiciones clave

- `runSigmaAlg` (línea ~1007): `let initState := EvalState.init input outputSize; let finalState := evalSigmaAlg ω LoopEnv.empty initState sigma; finalState.writeMem.toList.take outputSize`
- `EvalState.init` (línea ~995): `{ readMem := Memory.ofList input, writeMem := Memory.zeros outputSize }`
- `lowerFresh` (Sigma/Basic.lean:402): `(lower m n {} e).1`
- `lower` kron (Sigma/Basic.lean:290-311): tres ramas por `isIdentity`
- `adjustBlock` (Sigma/Basic.lean:247-254): `.compute k _ _ → .compute k (Gather.block blockIn v) (Scatter.block blockOut v)`
- `adjustStride` (Sigma/Basic.lean:257-266): `.compute k _ _ → .compute k {count:=nSize, baseAddr:=.var v, stride:=innerSize} {count:=mSize, baseAddr:=.var v, stride:=innerSize}`
- `evalMatExprAlg` kron (línea 2234-2268): tres ramas por `isIdentity`, I⊗B = flatMap de bloques, A⊗I = lanes interleaved
- `evalSigmaAlg.eq_2` = unfold loop case, `.eq_1` = compute, `.eq_3` = seq, `.eq_5` = temp
- `compute_loop_decompose_writeMem` (línea ~4291): writeMem extraction para compute loops
- `evalScatter_stride_var_eq` (línea ~4359): stride scatter to enumFrom form
- `stride_scatter_loop_inv` (línea ~4490): stride scatter loop invariant
- `evalGather_stride_ofList_eq_lane` (línea ~1897): stride gather = lane extraction
- `lowering_compute_contiguous_correct` (línea ~2533): runSigmaAlg .compute = evalKernelAlg
- `lower_kernel_preserves_length` (línea ~4305): kernel preserves length
- `lower_hasNoSeqLower_contiguous` (línea ~2801): lower of non-zero = .compute k contiguous
- `lower_hasNoSeqLower_state_eq` (línea ~2748): state independence
- `lower_hasNoSeqLower_notHasNoZero_is_nop` (línea ~2772): lower of zero = .nop

## Lecciones Aprendidas

### De sesiones anteriores (S-1 a S-3)
- **L-143**: `evalSigmaAlg` NO es monótona por `.temp` → `HasNoCompose` resuelve
- **L-153**: `HasNoCompose` como precondición precisa para kron
- **L-155**: `evalKernelAlg_length` — kernels preservan longitud
- **L-156**: `rw` antes de `apply` para igualdad definitional
- **L-161**: `lower_preserves_size_ge` falso cuando m₂=0 → precondición m>0
- **L-134-L-138**: DAG de-risking — Paso 2 es el nodo de-risk
- **L-SUBST**: NO usar `subst` en kron cases de gen theorems — destruye syntactic form para termination
- **L-PSIGMA**: PSigma packing de WF machinery renombra variables — resuelto con `induction mat generalizing`
- **L-HAVE-TYPE**: `have hst1 := ih ...` sin type annotation causa problemas con omega — usar `have hst1 : tipo := ih ...`
- **L-RENAME**: Después de `subst`, usar `rename_i` para recuperar variables inaccessibles (m₁✝ → m₁)
- **L-FRESHLOOP**: `simp [freshLoopVar]` necesario antes de `omega` para goals con freshLoopVar
- **L-BIND**: `rw [LoopEnv.bind_same]` cierra automáticamente goals de la forma `(env.bind v val) v < n` cuando `hi : val < n` está en contexto
- **L-LOOP-SEM**: `evalSigmaAlg` loop semantics DEBEN coincidir con `evalSigma` — NO sobreescribir readMem con writeMem
- **L-SIMP-VS-HAVE**: Wrapper simp-friendly para `.2` extracción (evita variables inaccesibles)
- **L-VALS-PLACEHOLDER**: Pasar `_` para vals en scatter_loop_wm_irrelevant
- **L-EVALSCATTER-ENUM**: Cadena: eq_2 → compute_loop_decompose_writeMem → evalScatter_block_eq_enumFrom → wm_irrelevant
- **L-STRIDE-INVARIANT**: Invariante modular: `p%m₂ < i → wm_i.toList[p]? = (vals(p%m₂))[p/m₂]?`
- **L-OMEGA-NONLINEAR**: omega no maneja `m₂ * (p/m₂)` — usar `Nat.div_add_mod`, `calc`, `nlinarith`
- **L-ZERO-ADD**: `Nat.zero_add` (0+k=k) vs `Nat.add_zero` (k+0=k)
- **L-UNFOLD-MEMORY**: `unfold Memory.toList Memory.size at *` para goals con Memory
- **L-LIST-NONE**: `apply List.getElem?_eq_none; unfold Memory.toList Memory.size at *; rw [Array.length_toList]; omega`

### Nuevas de esta sesión (S-4/S-5)

- **L-SIMP-AT-IH**: Cuando `simp only [f]` simplifica el goal pero no una hipótesis `ih`, causando type mismatch en `exact ih x`, añadir `at ih ⊢` → `simp only [f] at ih ⊢; exact ih x`. Esto es especialmente necesario en pruebas inductivas sobre `List.foldl_cons`.

- **L-MIN-DEF**: `Nat.min_eq_left` requiere `a ≤ b` y produce `min a b = a`. Pero si el goal tiene la dirección opuesta (`x = min a b`), `symm; apply Nat.min_eq_left` puede fallar si `symm` deja una forma no-unificable. Mejor usar `rw [Nat.min_def]; split_ifs with h` que funciona sin importar la dirección.

- **L-MATCH-SPLITTER**: `cases x <;> simp_all` puede fallar con "failed to generate splitter for match" cuando `x` es una función compleja como `MatExpr.isIdentity`. Usar `match h : x with | true => ... | false => ...` en su lugar.

- **L-BOOL-ITE**: Para reducir `if (false = true) then ... else ...`, `simp only [ite_false]` no basta — necesita `Bool.false_eq_true` primero. Full set: `simp only [ha_false, Bool.false_eq_true, ite_false, h_id_b, ite_true, ...]`.

- **L-RW-DEPENDENT**: `rw [h_eq]` inside `l[n]` (getElem) falla con "motive not type correct" cuando `h_eq : l = l'` y el proof de bounds depende de `l.length`. **Solución**: trabajar a nivel `?` (Option) — `rw [h_eq]` en `l[n]?` funciona sin problemas porque `getElem?` no tiene proof dependiente.

- **L-SUBST-NONLINEAR**: Después de `subst ha_sq; subst hb_sq` (que unifica m₁=n₁, m₂=n₂), los goals se simplifican mucho. Pero si se necesita `ha_sq` o `hb_sq` después, están destruidos. Asegurarse de `have h_copy := ha_sq` antes de `subst` si se necesitan después.

## Progreso Global

| Sesión | Sorry eliminados | Sorry restantes | Hallazgos clave |
|--------|-----------------|-----------------|-----------------|
| S-1 | P1 (termination) | 4 | `induction mat generalizing` resuelve WF |
| S-2 | P2 (2 sorry) + loop fix | 2 | Bug semántico en evalSigmaAlg loop |
| S-3 | P3 (kron wm irrelevance) | **1 declaration** | `simp only [wrapper_lemma]` para variables inaccesibles |
| S-4 | Reestructuración + I⊗B | **1 decl (2 sorry)** | Block scatter pattern funciona end-to-end |
| S-5 | A⊗I infra complete | **1 decl (2 sorry)** | Stride infra works but assembly pendiente |
| Próxima | A⊗I assembly + zero + A⊗B | **0** | Cerrar non-zero + zero + unreachable |

## Infraestructura de Lemas (inventario completo)

### Block scatter (I⊗B)
| Lema | Línea aprox | Propósito |
|------|-------------|-----------|
| `foldl_write_shifted` | ~4200 | Shifted foldl write equivalence |
| `evalScatter_block_eq_enumFrom` | ~4212 | evalScatter para block = enumFrom foldl |
| `flatMap_range_length` | ~4223 | Longitud de flatMap sobre range con componentes uniformes |
| `foldl_write_enumFrom_preserves_size` | ~4235 | Size preservation de foldl write con enumFrom |
| `scatter_enumFrom_general` | ~4170 | toList después de scatter = take ++ vals ++ drop |
| `block_scatter_loop_inv` | ~4252 | Loop invariant: toList = concat ++ drop |
| `block_scatter_loop_wm_irrelevant` | ~4301 | WriteMem irrelevance para block scatter |

### Stride scatter (A⊗I)
| Lema | Línea aprox | Propósito |
|------|-------------|-----------|
| `stride_writes_size` | ~4312 | Size preservation |
| `stride_writes_preserve_other` | ~4325 | No afecta posiciones fuera del patrón |
| `stride_writes_skip_pos` | ~4340 | Posiciones con módulo ≥ i intactas |
| `stride_writes_at_pos` | ~4355 | Posiciones correctas escritas |
| `stride_scatter_loop_inv` | ~4490 | Loop invariant: size + correctness por posición |
| `stride_scatter_loop_wm_irrelevant` | ~4550 | WriteMem irrelevance para stride scatter |

### Compute loop + Kernel
| Lema | Línea aprox | Propósito |
|------|-------------|-----------|
| `compute_loop_decompose` | ~4264 | readMem preserved + writeMem = foldl scatter |
| `compute_loop_decompose_writeMem` | ~4291 | Wrapper simp-friendly de .2 |
| `lower_kernel_preserves_length` | ~4305 | Kernels de HasNoSeqLower preservan longitud |
| `lowering_compute_contiguous_correct` | ~2533 | runSigmaAlg .compute = evalKernelAlg |

### Gather helpers
| Lema | Línea aprox | Propósito |
|------|-------------|-----------|
| `read_ofList_eq_getD` | 85 | Memory.read ∘ ofList = getD |
| `evalGather_block_ofList_eq_drop_take` | ~1777 | Block gather = drop/take |
| `evalGather_stride_ofList_eq_lane` | ~1897 | Stride gather = map getD stride |
| `evalGather_stride_eq` | ~2376 | Stride gather general form |

### Lower helpers
| Lema | Línea aprox | Propósito |
|------|-------------|-----------|
| `lower_hasNoSeqLower_contiguous` | ~2801 | lower non-zero = .compute k contiguous |
| `lower_hasNoSeqLower_state_eq` | ~2748 | State independence for lower |
| `lower_hasNoSeqLower_notHasNoZero_is_nop` | ~2772 | lower zero = .nop |

### WriteMem irrelevance (COMPLETADO)
| Lema | Línea aprox | Status |
|------|-------------|--------|
| `compute_writeMem_irrelevant` | ~4195 | ✅ Para .compute |
| `evalSigmaAlg_writeMem_irrelevant` | ~4448 | ✅ Para TODOS los constructores incl. kron |

## Plan de Referencia

El plan completo está en: `~/.claude/plans/iterative-forging-waterfall.md`

Resumen de progreso:
- [x] GATE: De-risk sketch
- [x] Paso 1-2: Reestructurar signatura + call site
- [x] Paso 3-4: Lemas auxiliares evalGather (block + stride)
- [x] Paso 6: I⊗B case completo
- [ ] Paso 7: A⊗I case — infra done, assembly + zero pendientes
- [ ] Paso 8: A⊗B unreachable (trivial)
