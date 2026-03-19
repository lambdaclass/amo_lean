# AMO-Lean Sorry Closure: Diagnosis & Strategy

## 1. Project State (Branch: Bitwise, Fase 22)

**MixedEMatchSoundness.lean** (577 LOC, 14 declarations, 3 pending sorry):
- `sameShapeSemantics_holds` PROVED (13-case exhaustive)
- `go_preserves_cv` PROVED (foldl over subpatterns with ih_fuel threading)
- `add_node_consistent` PROVED (HIT + MISS cases, in MixedAddNodeTriple.lean)
- `nodeEval_canonical` PROVED (evalOp_ext + consistent_root_eq)
- `applyRulesF_preserves_cv` PROVED (foldl over rule list)
- `instantiateF_sound patVar` PROVED (lookup + injection)
- `applyRuleAtF_preserves_cv condMet=false + instantiateF=none` PROVED

**7 remaining sorry's, 3 independent clusters:**

| ID | Line | Cluster | Description |
|----|------|---------|-------------|
| EMATCH-SOUND | 289 | A (independent) | ematchF correctness — induction on fuel+Pattern |
| CHILDREN-BND | 402 | B (cycle core) | childIds from go bounded by g''.uf.size |
| SHI' | 404 | B | ShapeHashconsInv preserved by g.add |
| VALUE | 407 | B | v'(root id) = Pattern.eval(.node skelOp subpats) |
| VALUE-CHAIN | 442 | C (blocked by A) | calc chain ematch→PatternSoundRule |
| INST-CV | 486 | D (blocked by B) | instantiateF_sound → CV for acc' → ih |
| MERGE-CV | 487 | D (blocked by B+C) | instantiateF_sound + value chain + merge_consistent |

**Dependency graph:**
```
EMATCH-SOUND ──────────────────→ VALUE-CHAIN ──→ MERGE-CV
CHILDREN-BND + SHI' + VALUE ──→ instantiateF_sound ──→ INST-CV + MERGE-CV
```

## 2. Previous Agent's Diagnosis (Confirmed)

The agent correctly identified:
- A **cycle** between instantiateF_sound and the 3 sorry's (CHILDREN-BND, SHI', VALUE)
- The cycle **breaks by augmenting go_preserves_cv** to track bounds on childIds
- EMATCH-SOUND is **independent** (~200 LOC, pure induction)
- VALUE-CHAIN is **mechanical** once EMATCH-SOUND exists (~15 LOC calc chain)

## 3. Winning Strategies (from sibling projects + lessons)

### Cluster A: EMATCH-SOUND (line 289) — ~200 LOC

**Source**: OptiSat `EMatchSpec.lean:349-462` (ematchF_sound_strong)

**Strategy**: Fuel-based structural induction + nested foldl over class nodes

```
Proof skeleton:
1. induction fuel with
   | zero => simp [ematchF] at hmem; contradiction ([] has no members)
   | succ n ih =>
     cases pat with
     | patVar pv =>
       -- ematchF extends σ with canonId
       -- substVal reads σ → returns v(root(canonId))
       -- root(canonId) = root(classId) by root_idempotent  ✓
     | node skelOp subpats =>
       -- ematchF iterates over eclass.nodes, filters by sameShape
       -- For matching node: matchChildren recurses on children
       -- Need auxiliary: matchChildren_sound (foldl over child pairs)
```

**Key auxiliary** (from OptiSat): `matchChildren_sound` — proves that matchChildren produces substitutions where each child's substVal agrees with the matched class value.

**Lessons applied**:
- L-383: SubstExtends pattern — prove eval correct for ALL extensions of σ
- L-381: SameShapeSemantics bridge between skeleton match and semantic equality
- L-390: foldl soundness via List induction with suffices

**Blocking lemma needed**: `substVal_agrees` — if g.uf.size ≤ g'.uf.size and v agrees on old indices, then substVal v g.uf σ = substVal v' g'.uf σ for σ-values in bounds. This is straightforward from root preservation + agreement.

### Cluster B: The Cycle (lines 402-407)

#### B.1: CHILDREN-BND (line 402)

**Root cause**: `go_preserves_cv` doesn't currently return bounds on the output childIds.

**Fix**: Augment `go_preserves_cv` to also return `∀ c ∈ childIds, c < g_final.unionFind.parent.size`.

This follows from:
1. Each `instantiateF` call returns `id < g'.uf.size` (from `add_node_consistent` output clause `(g.add node).1 < (g.add node).2.unionFind.parent.size`)
2. The foldl accumulates ids — previous ids are bounded by monotonicity (`Nat.lt_of_lt_of_le hbound hsize`)
3. The initial `ids₀ = []` has the trivial property

**Source pattern**: OptiSat `instantiateF_go_sound` (lines 556-672) threads bounds through each step.

**Concrete approach**: Create `go_preserves_cv_with_bounds` that strengthens the conclusion:
```lean
∃ v', CV g_final env v' ∧ VPMI g_final ∧ ShapeHashconsInv g_final ∧
  g₀.unionFind.parent.size ≤ g_final.unionFind.parent.size ∧
  (∀ i, i < g₀.unionFind.parent.size → v' i = v₀ i) ∧
  (∀ c ∈ childIds, c < g_final.unionFind.parent.size)  -- NEW
```

The proof mirrors `go_preserves_cv` exactly, adding one more conjunct in the cons case. From the ih_fuel call, we get `id₁ < g₁.uf.size`. From the recursive call, we get `∀ c ∈ rest_childIds, c < g_final.uf.size`. For `id₁`, use `Nat.lt_of_lt_of_le (id₁_bound) (size_mono_recursive)`.

**Key insight** (L-237): The forward preservation chain. Each step increases uf.size monotonically. Previous ids stay bounded by transitivity.

#### B.2: SHI' (line 404)

**Root cause**: `add_node_consistent` returns `VPMI (g.add node).2` but NOT `ShapeHashconsInv (g.add node).2`.

**Fix**: Add a new lemma `add_preserves_shi` to `MixedAddNodeTriple.lean`:

```lean
theorem add_preserves_shi (g : MGraph) (node : MNode)
    (hshi : ShapeHashconsInv g) :
    ShapeHashconsInv (g.add node).2
```

**Proof strategy** (from VR1CS `add_preserves_hashcons_classes_aligned`):
1. Unfold `EGraph.add`; split on hashcons hit/miss
2. **HIT**: hashcons and classes unchanged → `hshi` applies directly
3. **MISS**: hashcons gets one new entry (canonNode → newId), classes gets one new class
   - For lookups of old entries: use `HashMap.getElem?_insert_ne` → `hshi` applies, then `classes_get?_insert_ne` to find old class
   - For lookup of new entry (canonNode): `HashMap.getElem?_insert_self` → newId maps to singleton class containing canonNode

**Alternative**: Could also augment `add_node_consistent` to return SHI' as part of its 7-tuple. This is cleaner since the HIT/MISS split is already done there.

**Lessons applied**:
- L-690: SHI is NOT part of PostMergeInvariant — it's separate
- L-695: add HIT case needs hashcons integrity → already handled by existing `hshi` arg

#### B.3: VALUE (line 407)

**Root cause**: After `add_node_consistent`, we have `v'(root id) = NodeEvalM node env v'` but need `v'(root id) = Pattern.eval(.node skelOp subpats, constVal, substVal v g.uf σ)`.

**Strategy** (from OptiSat `InstantiateEvalSound_holds`, SuperTensor lines 2005-2200):

```
The chain:
1. v'(root id) = NodeEvalM (replaceChildren skelOp childIds) env v'
   -- From add_node_consistent hval'

2. NodeEvalM (replaceChildren skelOp childIds) env v'
   = evalMixedOp (replaceChildren skelOp childIds) env v'
   -- By definition of NodeEvalM

3. evalMixedOp (replaceChildren skelOp childIds) env v'
   = evalMixedOp skelOp env (fun c => v'(childIds[c]))
   -- By replaceChildren semantics + evalOp_ext

4. v'(childIds[j]) = v''(childIds[j])  for each j
   -- By hagree' (v' agrees with v'' on indices < g''.uf.size, and childIds are bounded)

5. v''(root g'' childIds[j]) = Pattern.eval(subpats[j], constVal, substVal v g.uf σ)
   -- THIS IS THE MISSING PIECE: needs go_preserves_cv_with_values

6. Pattern.eval(.node skelOp subpats, constVal, substVal v g.uf σ)
   = evalMixedOp skelOp env (fun j => Pattern.eval(subpats[j], ...))
   -- By definition of Pattern.eval for .node
```

**Key insight**: Step 5 requires augmenting `go_preserves_cv` AGAIN to also track per-child value equations. The full auxiliary becomes `go_sound`:

```lean
private theorem go_sound (n : Nat) (σ : Substitution) (env : MixedEnv)
    (ih_fuel : [full instantiateF IH]) (pats : List Pattern) ...
    (hgo : go σ n g₀ pats ids₀ = some (childIds, g_final)) :
    ∃ v', CV g_final env v' ∧ VPMI g_final ∧ ShapeHashconsInv g_final ∧
      g₀.uf.size ≤ g_final.uf.size ∧
      (∀ i, i < g₀.uf.size → v' i = v₀ i) ∧
      (∀ c ∈ childIds, c < g_final.uf.size) ∧              -- CHILDREN-BND
      childIds.length = ids₀.length + pats.length ∧         -- LENGTH
      (∀ j (hj : j < pats.length),                          -- VALUES
        v' (root g_final.uf (childIds[ids₀.length + j])) =
          Pattern.eval (pats[j]) constVal (substVal v₀ g₀.uf σ))
```

This single augmented `go_sound` resolves CHILDREN-BND, VALUE, and part of the cycle simultaneously.

**Lessons applied**:
- L-237: Forward preservation chain (v3(idA) = v2(idA) = v1(idA) = a.eval)
- L-482: Three-step simp for replaceChildren + evalOp reduction
- L-148: foldl_invariant with membership for size-dependent properties

### Cluster C: VALUE-CHAIN (line 442) — ~15 LOC

**Strategy**: calc chain, mechanical once EMATCH-SOUND exists

```lean
calc
  rhs_eval (substVal v g.uf σ)
    = rhs_eval (substVal v₀ g₀.uf σ)     := substVal_agrees ...
  _ = lhs_eval (substVal v₀ g₀.uf σ)     := (psrule.soundness ..).symm
  _ = v₀ (root g₀.uf classId)            := ematchF_sound ...
  _ = v (root g.uf classId)              := by rw [consistent_root_eq']; exact hagrees ...
```

**Blocking**: Only EMATCH-SOUND.

### Cluster D: INST-CV + MERGE-CV (lines 486-487) — ~20 LOC total

Once `instantiateF_sound` is fully proved (Cluster B resolved):

**INST-CV** (line 486): `roots equal → acc' has CV from instantiateF_sound, feed into ih`
```lean
obtain ⟨v', hcv', hpmi', hshi', _, _, _⟩ := instantiateF_sound fuel g₀ _ σ v₀ env hcv₀ hpmi₀ hshi₀ hbnd₀ _ _ h_inst
exact ih _ v' hcv' hpmi'
```

**MERGE-CV** (line 487): `instantiateF_sound + value chain + merge_consistent + ih`
```lean
obtain ⟨v', hcv', hpmi', _, hsize', hagree', hval'⟩ := instantiateF_sound ...
have hmerge := merge_consistent g' env v' hcv' hpmi' classId rhsId ...
obtain ⟨v'', hcv'', hpmi''⟩ := hmerge
exact ih _ v'' hcv'' hpmi''
```

The merge equality (`v'(root classId) = v'(root rhsId)`) follows from VALUE-CHAIN.

## 4. Recommended Execution Order

```
Phase 1 (Independent, parallelize):
  A. ematchF_sound (~200 LOC, independent)
  B.1. go_sound (augmented go_preserves_cv with bounds + values, ~40 LOC delta)

Phase 2 (Sequential, closes the cycle):
  B.2. add_preserves_shi (~30 LOC, or inline in add_node_consistent)
  B.3. VALUE: follows from go_sound + add_node_consistent composition (~20 LOC)
  → instantiateF_sound CLOSED

Phase 3 (Mechanical, sequential):
  C. VALUE-CHAIN: calc chain (~15 LOC)
  D. INST-CV + MERGE-CV: direct application (~20 LOC)
```

**Estimated total new code**: ~300-350 LOC (of which ~200 is ematchF_sound)

## 5. Key Lessons Referenced

| ID | Title | Applied to |
|----|-------|------------|
| L-690 | SHI separate from PostMergeInvariant | SHI' sorry |
| L-695 | add HIT needs hashcons integrity | SHI' proof structure |
| L-691 | Cross-project reuse for UF proofs | All clusters |
| L-390 | foldl soundness via List induction | go_sound, applyRuleAtF |
| L-235 | add_node_consistent as universal workhorse | CHILDREN-BND, VALUE |
| L-237 | Forward preservation chain | VALUE (child value threading) |
| L-383 | SubstExtends for sequential foldl | EMATCH-SOUND |
| L-381 | SameShapeSemantics bridge | EMATCH-SOUND |
| L-482 | replaceChildren + evalOp reduction | VALUE |
| L-148 | foldl_invariant with membership | go_sound |

## 6. Source Project Reference Map

| Sorry | OptiSat reference | SuperTensor reference | VR1CS reference |
|-------|-------------------|-----------------------|-----------------|
| EMATCH-SOUND | EMatchSpec:349-462 | — | — |
| CHILDREN-BND | EMatchSpec:556-672 (go_sound) | CoreSpec:1287-1313 | CoreSpec:1238-1264 |
| SHI' | AddNodeTriple (inline) | — | CoreSpec:1266-1302 |
| VALUE | EMatchSpec:680-762 | PipelineSoundness:2005-2200 | — |
| VALUE-CHAIN | EMatchSpec:873-894 | — | — |
| INST-CV/MERGE-CV | EMatchSpec:999-1086 | — | — |

## 7. Risk Assessment

| Sorry | Difficulty | Risk | Notes |
|-------|-----------|------|-------|
| EMATCH-SOUND | HIGH | MEDIUM | ~200 LOC, but well-understood from OptiSat |
| CHILDREN-BND | LOW | LOW | Augment existing go_preserves_cv |
| SHI' | LOW | LOW | Mechanical HIT/MISS split |
| VALUE | MEDIUM | MEDIUM | Needs careful child-value threading |
| VALUE-CHAIN | LOW | LOW | calc chain, mechanical |
| INST-CV | LOW | LOW | Direct application |
| MERGE-CV | LOW | LOW | Direct application + merge_consistent |

**Critical path**: EMATCH-SOUND (longest, ~200 LOC) and go_sound (medium, requires augmenting existing proof).
