# Insights: lowerNTTLoopStmt_evaluates — NTT Loop Soundness Proof

**Fecha**: 2026-03-29
**Dominio**: lean4
**Objetivo**: Probar que el NTT loop de 3 niveles anidados evalúa correctamente

## 1. Estructura exacta del Stmt generado

`lowerNTTLoopStmt` (VerifiedCodeGen.lean:821-887) produce:

```
Stmt.for_                                    -- OUTER: stage = 0..logN
  init:   assign(stage := 0)
  cond:   stage < logN
  step:   assign(stage := stage + 1)
  body:   seq(
    assign(half := 2^(logN-1) >> stage),
    Stmt.for_                                -- MIDDLE: group = 0..2^stage
      init:   assign(group := 0)
      cond:   group < (1 << stage)
      step:   assign(group := group + 1)
      body:   Stmt.for_                      -- INNER: pair = 0..half
        init:   assign(pair := 0)
        cond:   pair < half
        step:   assign(pair := pair + 1)
        body:   seq(
          assign(i := group * 2 * half + pair),
          assign(j := i + half),
          assign(tw_idx := stage * 2^(logN-1) + group * half + pair),
          load(a_val := data[i]),
          load(b_val := data[j]),
          load(w_val := twiddles[tw_idx]),
          BUTTERFLY (lowerDIFButterflyStmt, verified, fuel=3),
          store(data[i] := sum),
          store(data[j] := b_prime)
        )
  )
```

Variables: stage, group, pair, half, i, j, tw_idx, a_val, b_val, w_val + butterfly temps (.temp 0,1,2)

## 2. Cómo TrustLean evalúa for_

De `Core/Eval.lean:151-158`:
```lean
.for_ init cond step body =>
  match fuel with
  | 0 => some (.outOfFuel, env)
  | fuel' + 1 =>
    match evalStmt fuel' env init with
    | some (.normal, env') => evalStmt fuel' env' (.while cond (.seq body step))
    | other => other
```

**Clave**: `for_` desugara a `init; while(cond) { body; step }`. MISMO fuel para init Y while.

## 3. Patrón probado de TrustLean Bridge para loops

De `Bridge/Correctness.lean:276-379`, el patrón `while_loop_correct`:

```lean
theorem while_loop_correct (n : Nat) (lv : LoopVar) (body : ExpandedSigma)
    (hFresh : loopVarFresh lv body)
    (ihBody : ∀ state llEnv, fullBridge state llEnv →
      ∃ fuel llEnv', evalStmt fuel llEnv (expandedSigmaToStmt body) = some (.normal, llEnv') ∧ ...)
    (rem : Nat) (i : Nat) (hi : i + rem = n) ... :
    ∃ fuel llEnv', evalStmt fuel llEnv (.while ...) = some (.normal, llEnv') ∧ ...
```

Proof por **inducción sobre iteraciones restantes** (rem: Nat):
- Base (rem=0): condición falsa → exit
- Inductivo (rem=succ rem'): condición verdadera → ejecutar body → step → recursión con rem'
- **Fuel composition**: `totalFuel := max(fuelBody, fuelRem) + 1`
- **Escalar via `evalStmt_fuel_mono`**

`fuelBound` (Bridge/Compile.lean:116):
```lean
def fuelBound (.loop n _ body) := n + 1 + n * (fuelBound body + 1)
```

## 4. Base case: butterfly ya probado

`lowerDIFButterflyStmt_evaluates` (VerifiedCodeGen.lean:740-798):
- Fuel=3 (fijo, sin loops)
- Prueba: unfold 3 assigns + Solinas folds
- Necesita: disjointness de variables user vs temp

## 5. Estrategia de proof

### Approach A: Inducción directa sobre iteraciones (RECOMENDADO)

Probar 3 lemmas recursivos, uno por nivel de loop:

**Paso 1**: `innerLoop_correct` — por inducción sobre `half - pairIdx`
```lean
theorem innerLoop_correct (half : Nat) (pairIdx : Nat) (rem : Nat) (hrem : pairIdx + rem = half)
    (env : LowLevelEnv) (hPair : env (.user "pair") = .int pairIdx) ... :
    ∃ fuel env', evalStmt fuel env (.while (pair < half) (.seq innerBody pairStep)) = some (.normal, env')
```

**Paso 2**: `middleLoop_correct` — por inducción sobre `2^stage - groupIdx`
- IH: `innerLoop_correct` para el body

**Paso 3**: `outerLoop_correct` — por inducción sobre `logN - stageIdx`
- IH: `middleLoop_correct` para el body

**Paso 4**: Componer en `lowerNTTLoopStmt_evaluates`:
- Unfold lowerNTTLoopStmt → for_ structure
- Evaluate init (stage := 0)
- Apply outerLoop_correct con rem=logN

### Approach B: Existential fuel con fuelBound (ALTERNATIVO)

Definir:
```lean
def nttFuelBound (logN : Nat) : Nat :=
  -- Conservative: logN * (logN * 2^logN * 20)
  logN * logN * (2^logN) * 20 + logN + 1
```

Probar:
```lean
theorem lowerNTTLoopStmt_evaluates (logN p k c : Nat) (llEnv : LowLevelEnv)
    (hdata : ∀ i, ∃ v, llEnv (.array "data" i) = .int v)
    (htw : ∀ i, ∃ v, llEnv (.array "twiddles" i) = .int v) :
    ∃ fuel env', evalStmt fuel llEnv (lowerNTTLoopStmt logN p k c) = some (.normal, env')
```

Usa `nttFuelBound` como testigo existencial, luego inductión descendente.

## 6. Lecciones aplicables

| ID | Lección | Aplicación |
|----|---------|------------|
| L-305 | Nested induction (structural + fuel) | Inducción sobre rem (iteraciones), no fuel |
| L-311 | Three-Part Invariant (fuel, result, frame) | Existencial ∃ fuel, no bound concreto |
| L-728 | seq/ite/assign son fuel-free | Base case: butterfly (fuel=3), assign/load/store (fuel=0) |
| L-658 | While loop helper extraction | Extraer `while_loop_correct` como helper separado |
| L-625 | Use existential ∃ fuel, not concrete bounds | TrustLean pattern: `evalStmt_fuel_mono` escala |
| L-281 | Fuel = depth bound, not resource | Mismo fuel para init y while en for_ |

## 7. Helpers necesarios (~30 LOC total)

Todos triviales (1-3 líneas de simp):

1. **Freshness**: stage no se re-asigna en middle loop body, group no en inner body
2. **Condition eval**: `evalExpr env (.binOp .ltOp (.varRef (.user "stage")) (.litInt logN))` → `some (.bool (decide ...))`
3. **Step eval**: `evalStmt fuel env (.assign (.user "stage") (.binOp .add (.varRef (.user "stage")) (.litInt 1)))` → incrementa
4. **Load preservación**: `(env.update (.user "a_val") v) (.array "data" idx) = env (.array "data" idx)`
5. **Store semantics**: `(env.update_array "data" i v) (.array "data" j) = if i = j then v else env (.array "data" j)`

## 8. Archivos a modificar

| Archivo | Acción | LOC |
|---------|--------|-----|
| `VerifiedCodeGen.lean` | Agregar `lowerNTTLoopStmt_evaluates` + helpers después de `emitNTTRustFn` | ~200 |

**NO crear archivos nuevos.** Todo va en VerifiedCodeGen.lean después de la sección del NTT loop.

## 9. Estimación

- **Dificultad**: ALTA (3 niveles de inducción anidada)
- **LOC**: ~200 (40 por nivel + 30 helpers + 30 composición)
- **Sorry risk**: BAJO si se sigue el pattern de Bridge/Correctness.lean
- **Tácticas**: simp only, omega, exact, refine, cases (estándar)
