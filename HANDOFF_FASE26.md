# Handoff: Fase 26 — Spec-Driven Reduction Discovery

## Estado del proyecto

- **Branch**: `ultra`
- **Último commit**: `2f5a506` (feat(fase25): FRI/Poseidon complete)
- **Fases 22-25**: COMPLETAS, 0 sorry
- **Fase 26**: PLANIFICADA en ARCHITECTURE.md, 0 código escrito
- **Fase 27**: PLANIFICADA (Pipeline Soundness + Benchmarks)
- **Sorry total proyecto**: 1 (roundtrip_succeeds en RoundtripSoundness.lean — dead code, documentado)
- **Build**: 591 jobs, 0 errores

## Qué es Fase 26

El e-graph recibe `reduce(x) ≡ x mod p` como axioma y satura con operaciones bitwise para DESCUBRIR implementaciones de modular reduction, potencialmente mejores que Barrett/Montgomery/Solinas.

**Primer framework verificado de spec-driven reduction discovery.**

## Plan completo (en ARCHITECTURE.md, sección "Fase 26")

7 nodos, ~1200 LOC:

```
N26.1 ReduceSpecAxiom (FUND) → N26.3 ExplosionControl (CRIT) → N26.4 CandidateExtraction (CRIT) → N26.6 DiscoveryRunner (HOJA) → N26.7 IntegrationTests (HOJA)
N26.2 BitwiseVocabulary (FUND) → N26.3
N26.5 TacticVerification (PAR) → N26.6
```

Bloques: B107-B113.

## Nodos detallados

### N26.1 ReduceSpecAxiom (FUND, ~150 LOC, B107)
- **File**: `Discovery/ReduceSpecAxiom.lean`
- **What**: `ReduceSpec` structure + `insertReduceSpec` que inserta `reduce(x) ↔ x % p` como e-class equivalence en MixedEGraph
- **Key theorem**: `insertReduceSpec_preserves_cv`
- **Arithmetic domain**: `Nat` con bounds explícitos (`x < 2^w`)
- **De-risk**: sketch CV preservation antes del proof completo
- **Imports**: `AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec` (para ConsistentValuation), `AmoLean.EGraph.Verified.Bitwise.MixedExtract` (para MixedExpr)

### N26.2 BitwiseVocabulary (FUND, ~200 LOC, B108)
- **File**: `Discovery/BitwiseVocabulary.lean`
- **What**: Templates parametrizados de reglas bitwise:
  - Shift decomposition: `x = (x >> k) * 2^k + (x & (2^k - 1))`
  - Mask identity: `x & (2^w - 1) = x % 2^w`
  - Conditional sub: `if x ≥ p then x - p else x`
  - Barrett skeleton: `x - floor(x * m / 2^k) * p` (parametric in m, k)
  - Montgomery skeleton: `(x + (x * mu % R) * p) / R` (parametric in mu, R)
- **CRITICAL QA AMENDMENT**: Templates son parametrizados. Las constantes (m, k, mu, R) se pre-computan en N26.6, NO durante saturación. El e-graph ve reglas ya instanciadas.
- **Each rule**: `MixedSoundRule` con soundness probada sobre Nat con bounds
- **De-risk**: probar soundness de 1 regla (shift decomposition) antes de todas

### N26.3 ExplosionControl (CRIT, ~250 LOC, B109) — **GATE**
- **File**: `Discovery/SpecDrivenSaturation.lean`
- **What**: Extiende `GuidedSaturation` con 4 fases spec-driven:
  - Phase 0 (fuel 0-3): Solo spec axiom
  - Phase 1 (fuel 3-10): Algebraic rules (12 existentes)
  - Phase 2 (fuel 10-30): Field-specific + vocabulary
  - Phase 3 (fuel 30-40): Bitwise decomposition (CSD + shifts)
- **CRITICAL QA AMENDMENT**: Dynamic pruning — una vez que se encuentra una reducción completa (sin subterms `reduce`), su costo se convierte en el bound de poda. Antes de la primera solución: `known_best_cost * 1.5`.
- **Growth control**: `maxNodesBound > 5000 → abort`
- **Key theorem**: `specDrivenSaturateF_preserves_consistent`
- **De-risk**: testear con BabyBear que la saturación termina y produce ≥1 candidato

### N26.4 CandidateExtraction (CRIT, ~200 LOC, B110)
- **File**: `Discovery/CandidateExtraction.lean`
- **What**: `extractTopK` — extrae TOP-K candidatos (K=10) del e-graph saturado
- **Cada candidato**: una implementación bitwise de `x % p` (sin subterms `reduce`)
- **Cost ranking**: por HardwareCost (ARM scalar, NEON, AVX2)
- **Key theorem**: candidatos son semánticamente equivalentes a spec (heredado de CV)

### N26.5 TacticVerification (PAR, ~150 LOC, B111)
- **File**: `Discovery/TacticVerification.lean`
- **What**: Verificación automática de candidatos via tactic cascade
- **CRITICAL QA AMENDMENT**: Tri-state result:
  - `Verified(expr, cost)` — tactic probó `candidate(x) % p = x % p`
  - `FailedToVerify(expr, cost)` — tactic falló, logeado para inspección manual
  - `Rejected(reason)` — estructuralmente inválido
- **Tactic cascade**: `[native_decide, omega, ring, norm_num, simp [Nat.mod]]`
- **Smoke**: Solinas/Barrett/Montgomery conocidos clasifican como `Verified`

### N26.6 DiscoveryRunner (HOJA, ~150 LOC, B112)
- **File**: `Discovery/SpecDrivenRunner.lean`
- **What**: End-to-end `discoverReduction(p, hw) → List VerificationResult`
- **Pre-computation** (QA amendment): dado `(p, w)`, computa:
  - Barrett: `m = floor(2^k / p)` para k ∈ {w, 2w}
  - Montgomery: `mu = -p^{-1} mod 2^w`, `R = 2^w`
  - Solinas: si `p = 2^a - c`, extrae `(a, c)`
- **Instancia** los templates de N26.2 con las constantes pre-computadas
- **Comparison table**: discovered vs known costs

### N26.7 IntegrationTests (HOJA, ~100 LOC, B113)
- **File**: `Tests/NonVacuity/SpecDrivenDiscovery.lean`
- **Non-vacuity**: `discoverReduction` produce ≥1 `Verified` para BabyBear
- **Comparison**: discovered cost ≤ known best
- **Axiom audit**: `#print axioms` = 0 custom

## Infraestructura reutilizable (ya existe, NO reescribir)

| Componente | Archivo | Lo que provee |
|-----------|---------|--------------|
| `MixedSoundRule` | BitwiseRules.lean | Estructura para reglas con soundness |
| `GuidedSaturation` | Discovery/GuidedSaturation.lean | 3-phase saturation + autoAdjustConfig |
| `ShadowGraph` | Discovery/ShadowGraph.lean | Profitable filtering, cost tracking |
| `GrowthPrediction` | Discovery/GrowthPrediction.lean | maxNodesBound, safeFuel |
| `ShiftAddGen` | Discovery/ShiftAddGen.lean | CSD decomposition → shift-add rules |
| `RulerDiscovery` | RulerDiscovery.lean | CVec matching |
| `ConsistentValuation` | SemanticSpec.lean | CV definition + empty_consistent |
| `MixedEGraph` | MixedExtract.lean + others | E-graph type + operations |
| `extractF` | ExtractSpec.lean | Cost-optimal extraction |
| `HardwareCost` | CostModelDef.lean | ARM/NEON/AVX2 cost models |
| `selectReductionForBound` | CrossRelNTT.lean | Bound-aware reduction selection |

## Lecciones críticas

- **L-505**: distribute rule causa explosión exponencial → SIEMPRE `SaturationConfig` con limits
- **L-690**: SHI integrity para e-graph add — missing en OptiSat, necesita ser explícito
- **L-486**: kernel reduction depth para patterns complejos — `unfold + rfl`, no solo `rfl`
- **L-513**: compositional proofs ~30 LOC — descomponer en stages

## QA amendments ya integrados en el plan

1. **Templates + pre-computation**: N26.2 define templates parametrizados, N26.6 pre-computa constantes e instancia
2. **Dynamic pruning**: N26.3 usa best-found cost como bound (no static `2x`)
3. **Nat arithmetic domain**: proofs sobre Nat con bounds, lifting a BitVec como trabajo futuro
4. **Tri-state verification**: N26.5 no descarta silenciosamente candidatos que fallan tactic

## Protocolo de ejecución

1. **Scout** cada archivo antes de empezar (`scout.py`)
2. **FUND nodes secuenciales** con firewall `_aux`
3. **B109 (ExplosionControl) es GATE** — de-risk obligatorio antes de continuar
4. **Checkpoint compilación** después de cada nodo: `lake build` del archivo
5. **Wiring check** al cerrar cada bloque
6. **0 sorry** target — usar de-risk fallback (`native_decide` para primos < 2^31) si un theorem general es intractable
7. **NO modificar**: MixedNodeOp.lean, MixedEMatchSoundness.lean, MixedSemanticSpec.lean, PipelineSoundness.lean

## Cómo verificar que todo está bien antes de empezar

```bash
git log --oneline -3   # último: 2f5a506 (feat(fase25))
lake build 2>&1 | tail -3   # 591 jobs, 0 errors
grep -rn "sorry" AmoLean/EGraph/Verified/Bitwise/Discovery/ | grep -v "^.*:.*--"   # 0 sorry
```

## Target Discovery

| Prime | Known best | Discovery target |
|-------|-----------|-----------------|
| BabyBear (2^31 - 2^27 + 1) | Solinas fold (6 cycles) | ≤ 6 cycles or novel |
| Mersenne31 (2^31 - 1) | Solinas fold (3 cycles) | ≤ 3 cycles or novel |
| Goldilocks (2^64 - 2^32 + 1) | Solinas fold (8 cycles) | ≤ 8 cycles or novel |
| KoalaBear (2^31 - 2^24 + 1) | Solinas fold (5 cycles) | ≤ 5 cycles or novel |
