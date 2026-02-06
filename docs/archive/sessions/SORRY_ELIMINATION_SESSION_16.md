# Sesion 16: Compose Proof Completado + Documentacion

**Fecha**: 2026-02-05
**Modulo**: Verification/AlgebraicSemantics.lean
**Sesion anterior**: 15 (C-Lite++ strategy, base cases)

---

## Resumen Ejecutivo

| Metrica | Valor |
|---------|-------|
| **Logro principal** | Prueba formal de `lowering_compose_step` (~50 lineas) |
| **Axioma eliminado** | `lowering_compose_axiom` (reemplazado por prueba + 4 axiomas fundacionales) |
| **Axiomas agregados** | 4 (fundacionales, reutilizables para kron y otros casos) |
| **Teorema recursivo** | `lowering_algebraic_correct` ahora recursivo con `termination_by mat.nodeCount` |
| **maxHeartbeats** | 800000 (necesario para compose) |

---

## F1: Trabajo Realizado

### F1.S1: Prueba del Compose Step

#### F1.S1.C1: Problema

El caso compose del lowering correctness requeria probar:

```
runSigmaAlg ω (lowerFresh k n (.compose a b)) v k
= evalMatExprAlg ω k n (.compose a b) v
```

Donde:
- `lower (.compose a b) = .temp k_mid (.seq exprB exprA)` (ejecuta B primero, luego A)
- `evalMatExprAlg (.compose a b) v = evalMatExprAlg a (evalMatExprAlg b v)` (composicion funcional)

#### F1.S1.C2: Cadena de Prueba (13 pasos)

```
1. Unfold evalMatExprAlg      → RHS = a(b(v))
2. Set intermediate           → intermediate = b(v)
3. Unfold lowerFresh/lower    → .temp k_mid (.seq exprB exprA)
4. Unfold runSigmaAlg         → evalSigmaAlg chain
5. Apply eq_5 (temp), eq_3 (seq)  → explode seq semantics
6. dsimp only []              → simplify nested records
7. set stateB                 → name evaluation of exprB
8. IH_B unfold                → stateB.writeMem.take k_mid = intermediate
9. Size preservation          → stateB.writeMem.size = k_mid (axiom)
10. Take full length          → take = identity (List.take_of_length_le)
11. Memory roundtrip          → stateB.writeMem = Memory.ofList intermediate
12. WriteMem irrelevance      → replace wm with zeros k (axiom)
13. Alpha-equivalence         → replace state1 with {} (axiom)
14. Apply IH_A                → close by induction hypothesis
```

#### F1.S1.C3: Axiomas Fundacionales Introducidos

| Axioma | Proposito | Reutilizable? |
|--------|-----------|---------------|
| `evalSigmaAlg_writeMem_size_preserved` | Evaluar lowered expr no cambia tamano de writeMem | Si, para todos los casos |
| `evalSigmaAlg_writeMem_irrelevant` | Output (take m) no depende de writeMem inicial | Si, para compose y kron |
| `lower_state_irrelevant` | LowerState (IDs de loops) no afecta semantica | Si, para compose y kron |
| `evalMatExprAlg_length` | Output siempre tiene longitud m | Si, para todos los casos |

**Insight clave**: Estos 4 axiomas son mas fundamentales y reutilizables que el antiguo `lowering_compose_axiom` monolitico. Son propiedades estructurales del sistema, no especificas a compose.

#### F1.S1.C4: Teorema Recursivo

`lowering_algebraic_correct` se hizo recursivo:

```lean
theorem lowering_algebraic_correct
    (ω : α) (mat : MatExpr α k n) (v : List α) (hv : v.length = n) :
    runSigmaAlg ω (lowerFresh k n mat) v k = evalMatExprAlg ω k n mat v := by
  match mat with
  | .identity => ...
  | .dft => ...
  | .compose a b =>
    exact lowering_compose_step ω a b v hv
      (lowering_algebraic_correct ω b v hv)
      (fun w hw => lowering_algebraic_correct ω a w hw)
      (evalMatExprAlg_length ω b v hv)
  | _ => sorry
termination_by mat.nodeCount
```

**Eliminacion de IsPrimitiveRoot**: Los parametros `hω` y `hn` se eliminaron porque el lowering correctness es independiente de que omega sea raiz primitiva. Esto fue un insight del experto Lean (DeepSeek, Sesion 15).

### F1.S2: Helper Lemma

```lean
theorem Memory.ofList_toList (m : Memory α) : Memory.ofList m.toList = m := by
  cases m; simp only [Memory.ofList, Memory.toList]
```

Permite roundtrip: si conocemos `m.toList = l`, entonces `m = Memory.ofList l`.

---

## F2: Errores Encontrados y Corregidos

### F2.S1: Error 1 - rfl falla para WF-recursive

**Problema**: `rfl` y `unfold lower` fallan para funciones con `termination_by`:

```lean
-- FALLA:
theorem lower_compose_unfold : (lower k n state (.compose a b)).1 = ... := rfl

-- ERROR: "failed to generate unfold theorem for 'AmoLean.Sigma.lower'"
```

**Causa**: Well-founded recursion genera definiciones que el kernel no puede reducir para argumentos abstractos.

**Solucion**: Usar `simp only [lower]` que aplica los equation lemmas generados por Lean:

```lean
simp only [lower]  -- Funciona: usa equation lemmas, no reduccion del kernel
```

### F2.S2: Error 2 - Array.toList_length no existe

**Problema**: El nombre del lemma consultado no coincide con Lean 4 actual.

```lean
-- NO EXISTE:
rw [Array.toList_length]

-- CORRECTO:
rw [Array.length_toList]  -- arr.toList.length = arr.size
```

**Leccion**: Siempre verificar nombres con `#check` antes de usar.

### F2.S3: Error 3 - set/dsimp interaccion con let bindings

**Problema**: Despues de `rw [evalSigmaAlg.eq_5, evalSigmaAlg.eq_3]`, el goal contenia `let` bindings que impedian a `set` encontrar la subexpresion.

```lean
-- FALLA:
set stateB := evalSigmaAlg ω LoopEnv.empty { readMem := ..., writeMem := ... } exprB
-- Error: pattern not found
```

**Solucion**: Aplicar `dsimp only []` primero para eliminar las `let` bindings:

```lean
dsimp only []  -- Simplifica accesos a records anidados
set stateB := evalSigmaAlg ω LoopEnv.empty { readMem := ..., writeMem := ... } exprB
-- Funciona
```

### F2.S4: Error 4 - Doc comment antes de set_option

**Problema**: `/-- ... -/` docstring seguida de `set_option` causa error de parsing:

```lean
/-- The compose step. -/
set_option maxHeartbeats 800000 in
theorem lowering_compose_step ...
-- ERROR: "unexpected token 'set_option'; expected 'lemma'"
```

**Causa**: Doc comments deben preceder inmediatamente una declaracion (theorem, def, lemma), no `set_option`.

**Solucion**: Usar section comment `/-! ... -/` en lugar de doc comment:

```lean
/-! The compose step. -/
set_option maxHeartbeats 800000 in
theorem lowering_compose_step ...
-- OK
```

### F2.S5: Error 5 - List.take_length_le deprecated

**Problema**: `List.take_length_le` puede no existir o estar deprecated.

**Solucion**: Usar `List.take_of_length_le`:

```lean
exact List.take_of_length_le (le_of_eq h_toList_len)
```

---

## F3: Lecciones Aprendidas

### L-069: simp only [f] para WF-recursive Functions

Para funciones definidas con `termination_by`, `rfl` y `unfold` fallan. Usar `simp only [f]` que aplica los equation lemmas generados por el equation compiler.

### L-070: dsimp only [] para Eliminar let Bindings

Despues de `rw` con equation lemmas (ej: `evalSigmaAlg.eq_5`), el goal puede contener `let` bindings de Lean. `dsimp only []` las elimina sin hacer ninguna otra simplificacion.

### L-071: Memory Roundtrip Pattern

```lean
-- Si sabemos: m.toList = l
-- Entonces: m = Memory.ofList l
-- Via: Memory.ofList_toList + rewrite
have h_mem_eq : m = Memory.ofList l := by
  rw [← Memory.ofList_toList m, h_toList_eq]
```

### L-072: Axiomas Fundacionales > Axiomas Monoliticos

Reemplazar un axioma grande (lowering_compose_axiom) por 4 axiomas pequenos y fundamentales es superior:
- Los axiomas pequenos son mas faciles de auditar
- Son reutilizables para otros casos (kron, etc.)
- Reducen el TCB real (Trusted Computing Base)

### L-073: IsPrimitiveRoot NO se Necesita para Lowering

El lowering correctness (`runSigmaAlg = evalMatExprAlg`) es una propiedad puramente sintactica/semantica. No depende de que omega sea raiz primitiva. Esto permite hacer el teorema recursivo sobre `mat.nodeCount` sin restricciones.

### L-074: Equation Lemmas Numerados

`evalSigmaAlg` genera equation lemmas numerados:
- `evalSigmaAlg.eq_1` - compute
- `evalSigmaAlg.eq_2` - loop
- `evalSigmaAlg.eq_3` - seq
- `evalSigmaAlg.eq_4` - par
- `evalSigmaAlg.eq_5` - temp
- `evalSigmaAlg.eq_6` - nop

Uso: `rw [evalSigmaAlg.eq_5, evalSigmaAlg.eq_3]` para desplegar temp + seq.

### L-075: Compose Proof Architecture

La prueba de compose sigue un patron general:
1. Unfold ambos lados
2. Extraer intermediate value via IH_B
3. Probar que writeMem contiene el intermediate (size + take + roundtrip)
4. Usar writeMem irrelevance para normalizar
5. Usar alpha-equivalence para normalizar LowerState
6. Aplicar IH_A

Este patron es reutilizable para otros combinadores que usan `.seq`.

---

## F4: Estado Post-Sesion

### Cambios en AlgebraicSemantics.lean

| Seccion | Cambio |
|---------|--------|
| Part 2 | Agregado `Memory.ofList_toList` |
| Part 10 | Eliminado `lowering_compose_axiom` |
| Part 10 | Agregados 4 axiomas fundacionales |
| Part 11 | Agregado `lowering_compose_step` (prueba formal) |
| Part 12 | Actualizado `lowering_kron_axiom` (sin hω, hn) |
| Part 13 | `lowering_algebraic_correct` ahora recursivo |
| Part 13 | Agregado `termination_by mat.nodeCount` + `decreasing_by` |

### Metricas

| Metrica | Antes (Sesion 15) | Despues (Sesion 16) |
|---------|-------------------|---------------------|
| Axiomas en AlgebraicSemantics | 4 | 7 (+4 fund, -1 compose) |
| Sorries en AlgebraicSemantics | 1 | 1 (sin cambio, wildcard) |
| Teoremas probados | 5 base cases | 5 base + compose step |
| lowering_algebraic_correct | No recursivo | Recursivo (termination_by) |

### Compilacion

```
lake build  -- OK, 0 errors
```

---

## F5: Proximos Pasos

1. **Kron proof**: Requiere `lowering_kron_axiom` replacement con prueba formal
   - Dificultad: MUY ALTA (loop invariant + adjustBlock/adjustStride)
   - Axiomas fundacionales ya introducidos son reutilizables

2. **Wildcard cases**: perm, add, smul, zero, etc.
   - La mayoria son `compute` cases similares a identity/dft/ntt
   - Requieren lemmas de kernel evaluation

3. **Eliminacion de axiomas fundacionales**: Probar los 4 nuevos axiomas
   - `evalMatExprAlg_length`: MEDIA (induccion sobre MatExpr)
   - `lower_state_irrelevant`: MEDIA (induccion sobre MatExpr)
   - `evalSigmaAlg_writeMem_size_preserved`: MEDIA (induccion sobre SigmaExpr)
   - `evalSigmaAlg_writeMem_irrelevant`: ALTA (non-interference proof)

---

## F6: Archivos Modificados

| Archivo | Accion |
|---------|--------|
| `AmoLean/Verification/AlgebraicSemantics.lean` | Modificado: compose proof, axiomas, recursion |
| `docs/project/SORRY_INVENTORY.md` | Actualizado |
| `docs/project/SORRY_ELIMINATION_SESSION_16.md` | Creado |
| `docs/project/LECCIONES_QA.md` | Actualizado |
| `docs/project/SORRY_ELIMINATION_PLAN.md` | Actualizado |

---

## F7: Tecnicas de Desarrollo

### F7.S1: Exploracion en Scratch Files

Se usaron archivos temporales para explorar la prueba antes de integrar:
- `test_eq_lemmas.lean` - Descubrir equation lemma names
- `test_compose_v4.lean` - Primer intento con rfl (fallo)
- `test_compose_v5.lean` - Prueba exitosa validada

### F7.S2: fail "GOAL STATE" Technique

Para inspeccionar el estado del goal en puntos intermedios:

```lean
fail "STOP"  -- Muestra el goal state actual en el error message
```

Util cuando `#check` no ayuda y se necesita ver el goal exacto despues de varios rewrites.

### F7.S3: Build Verification

Despues de cada cambio significativo:

```bash
lake build AmoLean.Verification.AlgebraicSemantics 2>&1 | tail -5
```

Verificar que compila sin errores antes de continuar.
