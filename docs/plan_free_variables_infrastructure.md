# Plan: Infraestructura de Variables Libres para Alpha-Equivalencia

**Proyecto**: amo-lean
**Fecha**: 2026-02-06
**Archivo principal**: `AmoLean/Verification/AlgebraicSemantics.lean`
**Contexto**: Resolver el blocker del caso loop en `exactStructure_eval_eq`

---

## Problema Identificado

El caso loop en `exactStructure_eval_eq` no puede probarse con la IH actual:

```lean
| loop n v1 v2 body1 body2 _ ih =>
  -- IH da: ∀ env st, evalSigmaAlg ω env st body1 = evalSigmaAlg ω env st body2
  -- Necesitamos: evalSigmaAlg ω (env.bind v1 i) st' body1 = evalSigmaAlg ω (env.bind v2 i) st' body2
  -- ¡Pero v1 ≠ v2, así que los envs son DIFERENTES!
  sorry
```

**Insight clave**: Si `v1 ∉ fv(body1)` y `v2 ∉ fv(body2)`, entonces el binding no afecta la evaluación y podemos usar la IH.

---

## Consenso de Expertos (DeepSeek + Gemini QA)

Ambos expertos recomiendan:
1. Definir `fv : SigmaExpr → Finset LoopVar` (variables libres)
2. Probar `eval_ext` (evaluación solo depende de variables libres)
3. Fortalecer `ExactStructure.loop` con condición de freshness
4. Completar el caso loop usando la nueva infraestructura

---

## Fase 1: Infraestructura de Variables Libres

### F1.C1: Definir fv para IdxExpr, Gather, Scatter

```lean
/-- Variables libres en una expresión de índice -/
def IdxExpr.fv : IdxExpr → Finset LoopVar
  | .const _ => ∅
  | .var v => {v}
  | .add e1 e2 => e1.fv ∪ e2.fv
  | .mul e1 e2 => e1.fv ∪ e2.fv
  | .sub e1 e2 => e1.fv ∪ e2.fv
  | .div e1 e2 => e1.fv ∪ e2.fv
  | .mod e1 e2 => e1.fv ∪ e2.fv

/-- Variables libres en Gather -/
def Gather.fv : Gather → Finset LoopVar
  | .contiguous count base => base.fv
  | .strided count stride base => stride.fv ∪ base.fv
  | .block blockSize loopVar => {loopVar}
  | .indexed idxExpr => idxExpr.fv

/-- Variables libres en Scatter -/
def Scatter.fv : Scatter → Finset LoopVar
  | .contiguous count base => base.fv
  | .strided count stride base => stride.fv ∪ base.fv
  | .block blockSize loopVar => {loopVar}
  | .indexed idxExpr => idxExpr.fv
```

### F1.C2: Definir fv para SigmaExpr

```lean
/-- Variables libres en SigmaExpr -/
def SigmaExpr.fv : SigmaExpr → Finset LoopVar
  | .compute _ gather scatter => gather.fv ∪ scatter.fv
  | .loop _ v body => body.fv \ {v}  -- v está bound, no free
  | .seq s1 s2 => s1.fv ∪ s2.fv
  | .par s1 s2 => s1.fv ∪ s2.fv
  | .temp _ body => body.fv
  | .nop => ∅
```

### F1.C3: Probar propiedades básicas

```lean
-- fv es decidable
instance : DecidablePred (· ∈ expr.fv) := inferInstance

-- fv es finito
theorem fv_finite (expr : SigmaExpr) : expr.fv.Finite := Finset.finite_toSet _
```

---

## Fase 2: Lemma de Extensionalidad (eval_ext)

### F2.C1: eval_ext para IdxExpr

```lean
/-- Evaluar IdxExpr solo depende de las variables libres -/
theorem IdxExpr.eval_ext (e : IdxExpr) (env1 env2 : LoopEnv)
    (h : ∀ v ∈ e.fv, env1.lookup v = env2.lookup v) :
    evalIdxExpr env1 e = evalIdxExpr env2 e
```

### F2.C2: eval_ext para SigmaExpr (caso crucial)

```lean
/-- Evaluar SigmaExpr solo depende de las variables libres -/
theorem SigmaExpr.eval_ext (ω : α) (expr : SigmaExpr) (env1 env2 : LoopEnv) (st : EvalState α)
    (h : ∀ v ∈ expr.fv, env1.lookup v = env2.lookup v) :
    evalSigmaAlg ω env1 st expr = evalSigmaAlg ω env2 st expr
```

**Caso loop (el más importante)**:
```lean
| loop n v body =>
  -- fv(.loop n v body) = body.fv \ {v}
  -- Para cada i, necesitamos: env1.bind v i ≈ env2.bind v i en body.fv
  -- Si w ∈ body.fv y w ≠ v: (env1.bind v i).lookup w = env1.lookup w = env2.lookup w
  -- Si w = v: (env1.bind v i).lookup v = i = (env2.bind v i).lookup v
  -- Luego aplicamos IH
```

### F2.C3: Corolario para ignore_binding

```lean
/-- Si v ∉ fv(expr), el binding de v no afecta la evaluación -/
theorem eval_ignore_binding (ω : α) (expr : SigmaExpr) (env : LoopEnv) (st : EvalState α)
    (v : LoopVar) (val : Nat) (h : v ∉ expr.fv) :
    evalSigmaAlg ω (env.bind v val) st expr = evalSigmaAlg ω env st expr :=
  eval_ext ω expr _ _ (fun w hw => by
    simp [LoopEnv.lookup_bind]
    intro heq
    subst heq
    exact absurd hw h)
```

---

## Fase 3: Fortalecer ExactStructure

### F3.C1: Agregar freshness a ExactStructure.loop

```lean
/-- ExactStructure con condición de freshness -/
inductive ExactStructure : SigmaExpr → SigmaExpr → Prop
  | compute : ∀ k g s, ExactStructure (.compute k g s) (.compute k g s)
  | loop : ∀ n v1 v2 body1 body2,
      ExactStructure body1 body2 →
      v1 ∉ body1.fv →  -- freshness
      v2 ∉ body2.fv →  -- freshness
      ExactStructure (.loop n v1 body1) (.loop n v2 body2)
  | seq : ∀ s1a s1b s2a s2b,
      ExactStructure s1a s2a → ExactStructure s1b s2b →
      ExactStructure (.seq s1a s1b) (.seq s2a s2b)
  | par : ∀ s1a s1b s2a s2b,
      ExactStructure s1a s2a → ExactStructure s1b s2b →
      ExactStructure (.par s1a s1b) (.par s2a s2b)
  | temp : ∀ n body1 body2,
      ExactStructure body1 body2 →
      ExactStructure (.temp n body1) (.temp n body2)
  | nop : ExactStructure .nop .nop
```

### F3.C2: Probar que adjustBlock preserva freshness

```lean
/-- adjustBlock con variable fresca produce expresión donde esa variable es fresh -/
theorem adjustBlock_fresh (v : LoopVar) (n_in n_out : Nat) (expr : SigmaExpr)
    (h : v ∉ expr.fv) :
    v ∉ (adjustBlock v n_in n_out expr).fv :=
  -- adjustBlock solo AÑADE v a Gather.block/Scatter.block
  -- No introduce v como variable libre nueva
  sorry

/-- adjustBlock_produces_exactStructure con freshness -/
theorem adjustBlock_produces_exactStructure' (v : LoopVar) (n_in n_out : Nat)
    {expr1 expr2 : SigmaExpr} (h : SameStructure expr1 expr2)
    (hf1 : v ∉ expr1.fv) (hf2 : v ∉ expr2.fv) :
    ExactStructure (adjustBlock v n_in n_out expr1) (adjustBlock v n_in n_out expr2)
```

---

## Fase 4: Completar exactStructure_eval_eq

### F4.C1: Loop case usando eval_ext + freshness

```lean
theorem exactStructure_eval_eq (ω : α) {expr1 expr2 : SigmaExpr}
    (h : ExactStructure expr1 expr2) (env : LoopEnv) (st : EvalState α) :
    evalSigmaAlg ω env st expr1 = evalSigmaAlg ω env st expr2 := by
  induction h generalizing env st with
  | compute k g s => rfl
  | loop n v1 v2 body1 body2 hbody hf1 hf2 ih =>
    simp only [evalSigmaAlg]
    congr 1
    ext i
    -- Queremos: evalSigmaAlg ω (env.bind v1 i) st' body1 = evalSigmaAlg ω (env.bind v2 i) st' body2
    -- Por hf1: v1 ∉ body1.fv, así que eval ignora el binding de v1
    -- Por hf2: v2 ∉ body2.fv, así que eval ignora el binding de v2
    rw [eval_ignore_binding ω body1 env st' v1 i hf1]
    rw [eval_ignore_binding ω body2 env st' v2 i hf2]
    exact ih env st'
  | seq s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [evalSigmaAlg]
    rw [ih1, ih2]
  | par s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [evalSigmaAlg]
    rw [ih1, ih2]
  | temp n body1 body2 _ ih =>
    simp only [evalSigmaAlg]
    exact ih env { readMem := st.writeMem, writeMem := Memory.zeros n }
  | nop => rfl
```

---

## Diagrama de Dependencias

```
F1.C1: fv para IdxExpr/Gather/Scatter ──┐
                                        │
F1.C2: fv para SigmaExpr ───────────────┼──► F2.C1: IdxExpr.eval_ext
                                        │           │
F1.C3: Propiedades básicas ─────────────┘           │
                                                    ▼
                                            F2.C2: SigmaExpr.eval_ext
                                                    │
                                                    ▼
                                            F2.C3: eval_ignore_binding
                                                    │
        ┌───────────────────────────────────────────┘
        │
        ▼
F3.C1: ExactStructure con freshness ────► F3.C2: adjustBlock_fresh
                                                    │
                                                    ▼
                                          F4.C1: exactStructure_eval_eq (loop case)
                                                    │
                                                    ▼
                                          lower_state_irrelevant (kron case) ✓
```

---

## Verificación

```bash
# Después de cada fase:
lake build AmoLean.Verification.AlgebraicSemantics 2>&1 | tail -5

# Al completar F4:
grep "sorry" AmoLean/Verification/AlgebraicSemantics.lean | wc -l
# Objetivo: reducir sorries en exactStructure_eval_eq y lower_state_irrelevant
```

---

## Riesgos

| Riesgo | Probabilidad | Mitigación |
|--------|--------------|------------|
| `fv` no computa bien en Gather.block | BAJA | Verificar definición con #eval |
| LoopEnv.lookup_bind no existe | MEDIA | Definir si es necesario |
| adjustBlock introduce v en fv | MEDIA | Revisar definición de adjustBlock |
| Freshness difícil de probar para lower | ALTA | Probar que lower usa nextLoopVar++ |

---

*Plan creado: 2026-02-06*
*Basado en consenso DeepSeek + Gemini QA*
