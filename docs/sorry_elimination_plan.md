# Sorry Elimination Plan: AlgebraicSemantics.lean

**Proyecto**: amo-lean
**Archivo**: `AmoLean/Verification/AlgebraicSemantics.lean`
**Fecha de creacion**: 2026-02-07
**Estado**: Fase completada

---

## Objetivo

Eliminar el sorry bloqueante en el caso `loop` de `exactStructure_eval_eq` que impedia probar la equivalencia semantica de expresiones alpha-equivalentes.

## Problema Original

```lean
| loop n v1 v2 body1 body2 _ ih =>
  -- IH da: forall env st, evalSigmaAlg omega env st body1 = evalSigmaAlg omega env st body2
  -- Necesitamos: evalSigmaAlg omega (env.bind v1 i) st' body1 = evalSigmaAlg omega (env.bind v2 i) st' body2
  -- Pero v1 != v2, asi que los envs son DIFERENTES!
  sorry
```

**Insight clave**: Si `v1 not-in fv(body1)` y `v2 not-in fv(body2)`, entonces el binding no afecta la evaluacion y podemos usar la IH.

---

## Infraestructura Implementada

### Fase 1: Definiciones de Variables Libres

**Ubicacion**: Namespace `AmoLean.Sigma` en AlgebraicSemantics.lean (lineas 200-310)

#### F1.1: IdxExpr.fv
```lean
def IdxExpr.fv : IdxExpr -> Finset LoopVar
  | .const _ => empty
  | .var v => {v}
  | .affine _ _ v => {v}
  | .add e1 e2 => IdxExpr.fv e1 union IdxExpr.fv e2
  | .mul _ e => IdxExpr.fv e
```

#### F1.2: Gather.fv y Scatter.fv
```lean
def Gather.fv (g : Gather) : Finset LoopVar := IdxExpr.fv g.baseAddr
def Scatter.fv (s : Scatter) : Finset LoopVar := IdxExpr.fv s.baseAddr
```

#### F1.3: SigmaExpr.fv
```lean
def SigmaExpr.fv : SigmaExpr -> Finset LoopVar
  | .compute _ g s => Gather.fv g union Scatter.fv s
  | .loop _ v body => SigmaExpr.fv body \ {v}  -- v is bound, not free
  | .seq s1 s2 => SigmaExpr.fv s1 union SigmaExpr.fv s2
  | .par s1 s2 => SigmaExpr.fv s1 union SigmaExpr.fv s2
  | .temp _ body => SigmaExpr.fv body
  | .nop => empty
```

### Fase 2: Lemas de Extensionalidad

**Ubicacion**: Lineas 330-450

#### F2.1: evalIdxExpr_ext
```lean
theorem evalIdxExpr_ext (e : IdxExpr) (env1 env2 : LoopEnv)
    (h : forall v in IdxExpr.fv e, env1 v = env2 v) :
    evalIdxExpr env1 e = evalIdxExpr env2 e
```

#### F2.2: evalSigmaAlg_ext
```lean
theorem evalSigmaAlg_ext (omega : alpha) (expr : SigmaExpr) (env1 env2 : LoopEnv) (st : EvalState alpha)
    (h : forall v in SigmaExpr.fv expr, env1 v = env2 v) :
    evalSigmaAlg omega env1 st expr = evalSigmaAlg omega env2 st expr
```

#### F2.3: evalSigmaAlg_ignore_binding (Corolario clave)
```lean
theorem evalSigmaAlg_ignore_binding (omega : alpha) (expr : SigmaExpr) (env : LoopEnv) (st : EvalState alpha)
    (v : LoopVar) (val : Nat) (hv : v not-in SigmaExpr.fv expr) :
    evalSigmaAlg omega (env.bind v val) st expr = evalSigmaAlg omega env st expr
```

### Fase 3: Lemas de Freshness para adjustBlock

**Ubicacion**: Lineas 235-280

#### F3.1: Lema fuerte de subconjunto
```lean
theorem adjustBlock_fv_subset (v : LoopVar) (n_in n_out : Nat) (expr : SigmaExpr) :
    SigmaExpr.fv (adjustBlock v n_in n_out expr) subset {v}
```

**Insight**: Despues de adjustBlock, las unicas fv posibles son {v} porque Gather.block y Scatter.block solo usan v.

#### F3.2: Freshness para variables diferentes
```lean
theorem adjustBlock_fresh (v w : LoopVar) (n_in n_out : Nat) (expr : SigmaExpr)
    (hw : w != v) : w not-in SigmaExpr.fv (adjustBlock v n_in n_out expr)
```

#### F3.3: Preservacion de loopVarsOf
```lean
theorem adjustBlock_loopVarsOf (v : LoopVar) (n_in n_out : Nat) (expr : SigmaExpr) :
    SigmaExpr.loopVarsOf (adjustBlock v n_in n_out expr) = SigmaExpr.loopVarsOf expr
```

### Fase 4: Modificacion de ExactStructure

**Ubicacion**: Lineas 500-530

Se agrego condicion de freshness al constructor loop:

```lean
inductive ExactStructure : SigmaExpr -> SigmaExpr -> Prop
  | loop : forall n v1 v2 body1 body2,
      ExactStructure body1 body2 ->
      v1 not-in SigmaExpr.fv body1 ->  -- NUEVO: freshness
      v2 not-in SigmaExpr.fv body2 ->  -- NUEVO: freshness
      ExactStructure (.loop n v1 body1) (.loop n v2 body2)
  -- otros casos sin cambio...
```

### Fase 5: Prueba del caso loop

**Ubicacion**: Lineas 550-570

```lean
| loop n v1 v2 body1 body2 _ hf1 hf2 ih =>
  simp only [evalSigmaAlg]
  congr 1
  funext st' i
  have h1 : evalSigmaAlg omega (env.bind v1 i) st' body1 = evalSigmaAlg omega env st' body1 :=
    evalSigmaAlg_ignore_binding omega body1 env st' v1 i hf1
  have h2 : evalSigmaAlg omega (env.bind v2 i) st' body2 = evalSigmaAlg omega env st' body2 :=
    evalSigmaAlg_ignore_binding omega body2 env st' v2 i hf2
  have hih : evalSigmaAlg omega env st' body1 = evalSigmaAlg omega env st' body2 := ih env st'
  simp only [h1, h2, hih]
```

---

## Modificaciones Adicionales

### adjustBlock_produces_exactStructure

Actualizado para propagar las condiciones de freshness:

```lean
theorem adjustBlock_produces_exactStructure (v : LoopVar) (n_in n_out : Nat)
    {expr1 expr2 : SigmaExpr} (h : SameStructure expr1 expr2)
    (hfresh1 : forall w in SigmaExpr.loopVarsOf expr1, w != v)
    (hfresh2 : forall w in SigmaExpr.loopVarsOf expr2, w != v) :
    ExactStructure (adjustBlock v n_in n_out expr1) (adjustBlock v n_in n_out expr2)
```

### adjustBlock_lower_eval_eq

Actualizado para propagar freshness:

```lean
theorem adjustBlock_lower_eval_eq (omega : alpha) ...
    (hfresh1 : forall w in SigmaExpr.loopVarsOf e1, w != v)
    (hfresh2 : forall w in SigmaExpr.loopVarsOf e2, w != v) :
    evalSigmaAlg omega env st (adjustBlock v n_in n_out e1) =
    evalSigmaAlg omega env st (adjustBlock v n_in n_out e2)
```

---

## Diagrama de Dependencias Final

```
IdxExpr.fv, Gather.fv, Scatter.fv
            |
            v
      SigmaExpr.fv
            |
            +------> evalIdxExpr_ext
            |              |
            v              v
   adjustBlock_fv_subset   evalSigmaAlg_ext
            |                    |
            v                    v
   adjustBlock_fresh      evalSigmaAlg_ignore_binding
            |                    |
            v                    v
   ExactStructure.loop <---------+
   (con freshness)
            |
            v
   exactStructure_eval_eq (LOOP CASE CERRADO)
            |
            v
   adjustBlock_produces_exactStructure
   adjustBlock_lower_eval_eq
```

---

## Estado de Sorries Restantes

El caso loop de `exactStructure_eval_eq` esta completamente probado. Los sorries restantes en el archivo son:

1. `lower_state_irrelevant` - Requiere trabajo adicional en el caso `kron`
2. Lemas de SameStructure para lower - Dependen de semantica de lowering

---

## Lecciones Aprendidas

1. **Probar lema fuerte primero**: En lugar de probar directamente `w not-in fv(adjustBlock ...)`, fue mas facil probar `fv(adjustBlock ...) subset {v}` y derivar freshness.

2. **Namespaces y abbreviations**: Definir funciones en un namespace (`AmoLean.Sigma`) y crear abbreviations (`abbrev SigmaExpr.fv := ...`) permite usar notacion de campo fuera del namespace.

3. **Finset tactics**: Para goals sobre `Finset.mem_union`, usar `intro hmem` seguido de pattern matching sobre union, no `left`/`right`.

4. **congr + funext**: Para probar igualdad de funciones producidas por loops, usar `congr 1; funext st' i` para trabajar punto a punto.

---

*Documentacion creada: 2026-02-07*
*Basado en implementacion de plan_free_variables_infrastructure.md*
