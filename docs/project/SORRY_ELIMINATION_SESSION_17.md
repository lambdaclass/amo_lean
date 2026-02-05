# Sesion 17: Wildcard Sorry Eliminado

**Fecha**: 2026-02-05
**Archivo principal**: `AmoLean/Verification/AlgebraicSemantics.lean`
**Archivos auxiliares**: `AmoLean/Sigma/Basic.lean`, `AmoLean/Matrix/Basic.lean`

---

## Resumen Ejecutivo

| Metrica | Antes (S16) | Despues (S17) |
|---------|-------------|---------------|
| Sorry wildcard | 1 (10 cases) | 0 wildcard |
| Sorries explicitos | 0 | 3 (documentados) |
| Casos probados | 8 | 15 (+7 nuevos) |
| Axiomas | 7 | 8 (+1: `runSigmaAlg_seq_identity_compute`) |
| Axiomas kron | 1 | 1 (sin cambio) |
| Documentados como bug | 0 | 3 (add, transpose, conjTranspose) |

**Resultado neto**: Wildcard sorry eliminado. 15 de 18 casos de MatExpr cerrados.
3 casos documentados con analisis de por que no se pueden cerrar (decision DD-017).

---

## Trabajo Realizado

### F1: Quick Wins - Proofs Directos

#### F1.S1: Caso `.zero`
- `lower(.zero) = .nop`
- `evalSigmaAlg .nop` devuelve el estado inicial (Memory.zeros)
- Cierre via `zeros_toList` + `List.take_of_length_le`

#### F1.S2: Caso `.perm p`
- `lower(.perm) = .compute (.identity n) contiguous`
- `applyPerm p v = v` (stub en evalMatExprAlg)
- Misma estrategia que `.diag` (ya probado)

### F2: Axioma + 5 Casos via seq_identity

#### F2.S1: Nuevo axioma
```lean
axiom runSigmaAlg_seq_identity_compute
    (ω : α) (innerExpr : SigmaExpr) (kern : Kernel) (s outputSize : Nat)
    (v : List α)
    (hk : ∀ w, evalKernelAlg ω kern w = w) :
    runSigmaAlg ω (.seq innerExpr
      (.compute kern (Gather.contiguous s (.const 0))
                     (Scatter.contiguous s (.const 0)))) v outputSize
    = runSigmaAlg ω innerExpr v outputSize
```

**Justificacion**: Si un kernel devuelve su input sin cambios, aplicar `.compute` con gather/scatter contiguos despues de un `.seq` es un no-op. El axioma es auditablemente correcto.

#### F2.S2: 5 casos cerrados
Todos siguen el mismo patron:
1. `simp only [evalMatExprAlg, lowerFresh, lower]` - unfold
2. `rw [runSigmaAlg_seq_identity_compute ω _ kernel ...]` - elimina compute
3. `exact lowering_algebraic_correct ω a v hv` - recursion (IH)

| Caso | Kernel | evalKernelAlg = id |
|------|--------|-------------------|
| `.smul c a` | `.scale` | Si |
| `.elemwise op a` | `.sbox (k*n) op.toExp` | Si |
| `.partialElemwise idx op a` | `.partialSbox (k*n) op.toExp idx` | Si |
| `.mdsApply name sz a` | `.mdsApply name sz` | Si |
| `.addRoundConst round sz a` | `.addRoundConst round sz` | Si |

### F3: Sorry Documentados (3 casos)

#### `.add a b` - BUG SEMANTICO
- `lower(.add) = .par exprA exprB`
- `.par` ejecuta secuencialmente: resultado = `b(a(v))`
- `evalMatExprAlg(.add)` = suma pointwise: resultado = `a(v) + b(v)`
- Estos son diferentes; axiomatizar seria **unsound**
- Fix requiere: nuevo constructor SigmaExpr o rediseno de `.par`

#### `.transpose a` - MISMATCH DIMENSIONAL
- `lower` intercambia (k,n) → `lower n k`
- `runSigmaAlg` usa `outputSize = k`
- IH da `outputSize = n`
- Falla cuando `k != n`

#### `.conjTranspose a` - Mismo que transpose

### F4: Fix Tecnico - ElemOp.toExp

**Problema**: Inline `match op with | .pow e => e | .custom _ => 1` dentro del cuerpo de `lower` (WF-recursive) impedia la generacion del equation lemma. `simp only [lower]` fallaba para TODOS los casos.

**Diagnostico**: `#check @lower.eq_def` reportaba "failed to generate unfold theorem".

**Solucion**: Extraer match a funcion auxiliar `ElemOp.toExp`:
```lean
def ElemOp.toExp : ElemOp → Nat
  | .pow e => e
  | .custom _ => 1
```

Y reemplazar en `Sigma/Basic.lean`:
```lean
-- Antes (roto):
(.sbox (m * n) (match op with | .pow e => e | .custom _ => 1))
-- Despues (funciona):
(.sbox (m * n) op.toExp)
```

### F5: Documentacion

- `Theorems.lean`: Header de SUPERSEDED agregado
- `SORRY_INVENTORY.md`: Actualizado (25 sorries, 25 axiomas)
- `SORRY_ELIMINATION_PLAN.md`: Tabla C-Lite++ actualizada
- `LECCIONES_QA.md`: L-077 (inline match rompe eq lemmas)

---

## Decision de Diseno: DD-017

**Fecha**: 2026-02-05
**Contexto**: 10 sorry cases restantes en lowering_algebraic_correct
**Decision**: Cerrar 7 (2 proofs + 5 axiomatizados), dejar 3 como sorry documentados
**Justificacion**:
- `.add`: Bug semantico confirmado (.par != suma). Axiomatizar seria **unsound**.
- `.transpose`/`.conjTranspose`: Mismatch dimensional. Axiomatizar seria potencialmente **unsound** para matrices no cuadradas.
- No introducir axiomas falsos es mas importante que tener 0 sorries.
**Consecuencia**: El proyecto mantiene integridad logica a costa de 3 sorries documentados.

---

## Leccion Aprendida: L-077

> En funciones WF-recursive (con `termination_by`), NUNCA usar inline `match` dentro del cuerpo de un caso. Siempre extraer a funcion auxiliar. El generador de equation lemmas de Lean 4 no maneja case splits dentro de case arms. El fallo afecta a TODOS los equation lemmas de la funcion, no solo al caso con inline match.

---

## Archivos Modificados

| Archivo | Cambio |
|---------|--------|
| `AmoLean/Matrix/Basic.lean` | +`ElemOp.toExp` helper |
| `AmoLean/Sigma/Basic.lean` | `.elemwise`/`.partialElemwise`: inline match → `op.toExp` |
| `AmoLean/Verification/AlgebraicSemantics.lean` | +1 axioma, 10 casos explicitos (7 cerrados, 3 sorry) |
| `AmoLean/Verification/Theorems.lean` | Header SUPERSEDED |
| `docs/project/SORRY_INVENTORY.md` | Actualizado |
| `docs/project/SORRY_ELIMINATION_PLAN.md` | Actualizado |
| `docs/project/LECCIONES_QA.md` | +L-077 |
| `docs/project/SORRY_ELIMINATION_SESSION_17.md` | Nuevo |
