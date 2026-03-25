# AMO-Lean: Discovery Engine — Plan v3.3 + Hallazgos Creativos

## Fecha: 2026-03-17
## Versión target: v3.3.0

---

## 1. La Visión Original (Gemini QA)

> "Inyectar axiomas específicos de BabyBear/Mersenne31 como reglas de reescritura en tu e-graph.
> Dejar que el e-graph corra durante horas buscando trucos a nivel de bit que a un humano no se le ocurrirían."

**Lo que construimos hasta v3.2.4**:
- Alternativa A (v3.1): E-graph VERIFICA trucos bitwise conocidos → 1,744 LOC, 0 sorry
- Alternativa B (v3.2): E-graph SINTETIZA la mejor reducción dado primo p + hardware → 2,100 LOC, 0 sorry
- Alternativa C parcial (v3.2.4): C codegen verificado via Trust-Lean + BitVec bridge → 2,090 LOC, 0 sorry
- **Total Bitwise/: 5,180 LOC, 18 archivos, ~221 teoremas, 0 sorry, 0 axiomas**

**Lo que FALTA para la visión de Gemini**: El E-graph no "descubre" — instancia patrones conocidos.

---

## 2. Cómo Funciona AMO-Lean HOY (Modo Operativo)

### Input → Output actual

```
Input:  #eval synthesizeAndEmitC (2^31 - 2^27 + 1) arm_cortex_a76
        (primo BabyBear, target ARM)

Paso 1: detectSolinasForm analiza estructura binaria del primo
        → SolinasConfig { a = 31, b = 27 }

Paso 2: deriveFieldFoldRule crea regla de fold (PATTERN CONOCIDO)
        fold(x) = (x >>> 31) * (2^27 - 1) + (x &&& (2^31 - 1))

Paso 3: Conversión a MixedExpr → CodegenExpr → C code

Output: uint64_t reduce(uint64_t x) { return ((134217727 * (w_0 >> 31)) + (w_0 & 2147483647)); }
```

**Lo que NO pasa**: El E-graph NO satura buscando alternativas. La estrategia fue elegida por `detectSolinasForm`, no descubierta.

### Reglas actuales: ~25 total

| Categoría | Cantidad | Ejemplo |
|-----------|----------|---------|
| Algebraicas (identidad) | 6 | x + 0 → x, x * 1 → x |
| Algebraicas (distribución) | 4 | a*(b+c) → a*b + a*c |
| Bitwise genéricas | 10 | (x>>>a)>>>b → x>>>(a+b) |
| Field fold (Solinas) | 3 | x%p → fold(x) para 3 primos |
| **Total** | **23** | |

**Para descubrimiento real: necesitamos ~80-100+ reglas.**

---

## 3. Hallazgos de Proyectos Hermanos (Código Reutilizable)

### 3.1 SuperTensor-lean — 3 técnicas anti-explosión

| Técnica | LOC | Efecto | Transferible |
|---------|-----|--------|-------------|
| **Circuit Pruning** (CircuitPrune.lean) | ~300 | Reduce E-graph 30-50% pre-ILP | Sí — podar nodos dominados |
| **Region Partitioning** (Regions.lean) | ~400 | Ventanas de 500 clases, escala a 50K+ nodos | Sí — para FRI/NTT largo |
| **MCTS Heuristics** (MCTS.lean) | ~500 | UCB1 guía exploración, reduce 40-60% nodos explorados | Parcial — Rule Scoring UCB1-lite |

### 3.2 VR1CS-Lean — Growth Bound Theorem

```lean
-- Teorema de cota superior de crecimiento:
nodes ≤ initialNodes × (numRules + 1)^steps
```
Permite PREDECIR si la saturación va a explotar ANTES de correrla.

### 3.3 OptiSat + DynamicTreeProg — Treewidth DP Extraction

- `dp_optimal_of_validNTD`: extracción probadamente ÓPTIMA (0 sorry)
- Polynomial time: O(n · 2^tw) para treewidth ≤ 15
- **122 teoremas** en DynamicTreeProg, copiables/adaptables
- Routing automático: tw ≤ 15 → DP, else → ILP

### 3.4 TrustHash — Dual Representation Pattern

- `chi5` (BitVec 5) ↔ `chiNat` (Nat): dos representaciones con bridge
- `CipherBridge.lean`: validar que C code usa mismos parámetros que spec
- Patrón transferido → `BitVecBridge.lean` en v3.2.4 (592 LOC, 33 teoremas)

### 3.5 Trust-Lean — Verified C Pipeline

- `stmtToMicroC_correct`: forward simulation verificada (Stmt → MicroC)
- `microCToString` roundtrip: parse(emit(mc)) = mc
- Plonky3 bridges: Mersenne31, BabyBear, KoalaBear, Goldilocks como MicroC programs
- **14,690 LOC, 312 teoremas, 0 sorry** — pipeline completo desde IR hasta C

---

## 4. Estrategias Anti-Explosión (Creatividad)

### 4.1 Guided Saturation (reemplaza Cascade — mejora de QA)

En vez de 3 E-graphs separados: **1 E-graph unificado con activación faseada de reglas**.

```
Phase 1 (fuel 0-10):   Solo algebraic rules (12 reglas)
Phase 2 (fuel 10-40):  Unfreeze bitwise + shift-add + congruence (50+ reglas)
Phase 3 (fuel 40-50):  Unfreeze scheduling + lazy reduction (10 reglas)
```

**Ventaja**: Las reglas de Phase 2 VEN las equivalencias de Phase 1. No hay pérdida de optimalidad global.

**Por qué es mejor que Cascade**: Si una simplificación bitwise habilita una nueva factorización algebraica, Cascade la pierde (algebraic phase terminó). Guided Saturation la encuentra.

### 4.2 Shadow Graph (grafo dual de costos)

HashMap lightweight que trackea costo mínimo por e-class:

```
Antes de aplicar regla al E-graph:
  1. Simular en shadow: ¿reduce costo?
  2. Si new_cost >= current_min: SKIP
  3. Si new_cost < current_min: aplicar al E-graph real
```

Efecto: E-graph solo crece cuando hay mejora REAL de costo. Elimina ~60% de reglas que generan equivalentes más caros.

### 4.3 Rule Scoring UCB1-lite

```lean
score(rule) = expectedCostDelta / numMatches + C * sqrt(ln(totalApps) / ruleApps)
```
- Exploitation: reglas que reducen más costo
- Exploration: reglas poco probadas (pueden sorprender)
- Top-K selection: solo las mejores K reglas por iteración

### 4.4 Growth Prediction (antes de saturar)

```lean
predictedNodes ≤ initialNodes × (numRules + 1)^fuel
```
Si predicción > maxNodes: reducir fuel o activar fewer rules per phase.

### 4.5 CSD para Shift-Add (Canonical Signed Digit)

Descomponer constantes en mínimos non-zero bits:
```
134217727 = 2^27 - 1     → CSD: +2^27 -2^0     → (x<<<27) - x  (2 ops)
15 = 2^4 - 1             → CSD: +2^4 -2^0      → (x<<<4) - x   (2 ops)
13 = 2^4 - 2^2 + 1       → CSD: +2^4 -2^2 +2^0 → (x<<<4) - (x<<<2) + x (4 ops)
```
CSD garantiza la menor cantidad de operaciones shift-add-sub.

---

## 5. El "Descubrimiento" Concreto

### Ejemplo: BabyBear en RISC-V

Hoy (`synthesizeReduction`):
```
hi * (2^27 - 1) + lo    — costo: MUL(3) + AND(1) + SHIFT(1) + ADD(1) = 6 ciclos
```

Con E-graph discovery (v3.3):
```
Phase 2: ShiftAdd rule fires: hi * (2^27-1) → (hi<<<27) - hi
Resultado: (hi<<<27) - hi + lo  — costo: SHIFT(1)*2 + SUB(1) + AND(1) + ADD(1) = 5 ciclos
```

**Ahorro: 1 ciclo por reducción.** En un proof ZK con 10^6 reducciones: 1 segundo.

### Ejemplo: Primo nuevo p = 2^61 - 1 (Mersenne)

Hoy: `detectSolinasForm` falla (b=0, no es pseudo-Mersenne).

Con v3.3:
```
1. CongruenceGen genera: 2^61 ≡ 1 (mod p) — regla fold pura
2. ShiftAddGen: no multiplications needed (c=1, fold es suma)
3. E-graph descubre: x%p = (x>>>61) + (x &&& mask61), normalizar
4. Costo: SHIFT(1) + AND(1) + ADD(1) = 3 ciclos (óptimo teórico)
```

---

## 6. Plan v3.3 — Fase 24: E-Graph Discovery Engine

### DAG

```
N24.1 ShiftAddGen (FUND) ──→ N24.5 GuidedSaturation (CRIT)
N24.2 CongruenceGen (FUND) ──→
N24.3 LazyReduction (PAR) ──→
N24.4 ShadowGraph (FUND) ──→ N24.5
N24.6 RuleScoring (PAR) ──→ N24.5
N24.7 GrowthPrediction (PAR) ──→ N24.5
N24.8 TreewidthDP (CRIT) ──→ N24.9 DiscoveryPipeline (HOJA)
N24.5 ──→ N24.9
N24.9 ──→ N24.10 DiscoveryTests (HOJA)
```

### Nodos

| Node | Name | Type | LOC | Content |
|------|------|------|-----|---------|
| N24.1 | ShiftAddGen | FUND | ~300 | CSD decomposition, x*c → shifts+adds, soundness proofs |
| N24.2 | CongruenceGen | FUND | ~250 | 2^k ≡ c_k (mod p) for bounded k range, soundness proofs |
| N24.3 | LazyReduction | PAR | ~250 | Defer mod p with verified interval analysis (maxAbsValue) |
| N24.4 | ShadowGraph | FUND | ~250 | Cost-delta tracking, skip non-improving rules |
| N24.5 | GuidedSaturation | CRIT | ~400 | Phased rule activation in single E-graph, fuel=50 |
| N24.6 | RuleScoring | PAR | ~200 | UCB1-lite, top-K selection per iteration |
| N24.7 | GrowthPrediction | PAR | ~200 | maxNodesBound theorem, auto fuel/budget adjustment |
| N24.8 | TreewidthDP | CRIT | ~500 | Copy from DynamicTreeProg, polynomial optimal extraction |
| N24.9 | DiscoveryPipeline | HOJA | ~300 | Compose generate→predict→saturate→extract, discovery_sound |
| N24.10 | DiscoveryTests | HOJA | ~250 | 4 primes, does E-graph find shift-add for BabyBear? |
| **Total** | | | **~2,900** | |

### Blocks

| Block | Nodes | Execution |
|-------|-------|-----------|
| B89 | N24.1 ShiftAddGen | FUND sequential |
| B90 | N24.2 CongruenceGen | FUND sequential |
| B91 | N24.3, N24.6, N24.7 | PAR parallel |
| B92 | N24.4 ShadowGraph | FUND sequential |
| B93 | N24.5 GuidedSaturation | CRIT sequential (after all B89-B92) |
| B94 | N24.8 TreewidthDP | CRIT sequential (independent) |
| B95 | N24.9 DiscoveryPipeline | HOJA (after B93+B94) |
| B96 | N24.10 DiscoveryTests | HOJA |

### Key Design Decisions (from QA)

1. **Guided Saturation** (NOT Cascade): 1 E-graph, phased rule activation → no loss of global optimality
2. **CSD** for shift-add decomposition → provably minimal non-zero bits
3. **Synthesis-by-Verification**: generator proposes → Lean proves → only verified rules admitted
4. **Congruence bounded**: k ∈ [bitWidth-2..2*bitWidth+2] (~10 rules, not 128)
5. **Shadow Graph operational** (outside TCB) — extraction still verified via extractF_correct
6. **Lazy Reduction with `maxAbsValue`**: verified interval analysis, condition `max(a)+max(b) < 2^w - p`

---

## 7. Versión History del Roadmap Bitwise

| Version | Fase | Capacidad | LOC |
|---------|------|-----------|-----|
| v3.1.0 | 21 | E-graph VERIFICA trucos bitwise conocidos | 1,744 |
| v3.2.0 | 22 | E-graph SINTETIZA reducción óptima por primo + hardware | 2,100 |
| v3.2.4 | 23 | Verified C codegen via Trust-Lean + BitVec bridge | 2,090 |
| **v3.3.0** | **24** | **E-graph DESCUBRE reducción óptima con 80+ reglas** | **~2,900** |
| **Total** | | | **~8,834** |
