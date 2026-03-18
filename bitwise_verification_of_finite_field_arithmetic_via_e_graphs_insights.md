# Insights: Bitwise Verification of Finite Field Arithmetic via E-graphs for ZK Proofs

**Fecha**: 2026-03-16
**Dominio**: lean4
**Estado del objeto**: upgrade (AMO-Lean v3.0.0 → v3.1.0)
**Profundidad**: deep (Waves 1-8)

---

## 1. Analisis del Objeto de Estudio

### Resumen

Extender AMO-Lean v3.0.0 para soportar verificacion formal de operaciones bitwise en aritmetica de campos finitos, integrandolas en el motor E-graph verificado existente. El objetivo es que el E-graph pueda verificar que implementaciones bitwise conocidas (Montgomery REDC, Barrett reduction, Mersenne folding) son semanticamente equivalentes a la aritmetica algebraica abstracta (`a * b % p`). Esto habilita la verificacion automatica de trucos de bits campo-especificos para Mersenne31, BabyBear y Goldilocks.

### Keywords

1. `CircuitNodeOp` — inductive de operaciones del E-graph (extension principal)
2. `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight` — ops bitwise Lean 4
3. `NodeOps` / `NodeSemantics` — typeclasses para E-graph generico
4. `SoundRewriteRule` — regla de reescritura con prueba de soundness
5. `ConsistentValuation` — invariante de satisfacibilidad del E-graph
6. Montgomery REDC — reduccion via shifts/AND (R=2^k)
7. Barrett reduction — shifts + multiplicacion + reciprocal precomputado
8. Mersenne31 folding — `x % (2^31-1) = (x & mask) + (x >> 31)`
9. Equality saturation — saturacion de equivalencias algebraicas
10. Translation validation — Level 2 soundness (`cryptoEquivalent`)
11. `ZMod` bridging — conexion `Nat` bitwise <-> `ZMod p`
12. Fiat-Crypto — sintesis verificada de aritmetica modular (competidor/referencia)
13. `Nat.and_two_pow_sub_one_eq_mod` — LEMA PUENTE CLAVE: `x &&& (2^n-1) = x % 2^n`
14. E-graph explosion control — Herbie's 3 anti-explosion mechanisms
15. CryptOpt — equivalence checker via E-graph (no optimizer)

### Estado

**Upgrade de v3.0.0** — el proyecto tiene 160 archivos Lean, ~60,000 LOC, 0 sorry, 0 axiomas custom. El motor E-graph opera sobre `CircuitNodeOp` con 7 constructores PURAMENTE algebraicos. Los 3 campos finitos (Mersenne31, BabyBear, Goldilocks) estan formalizados con `toZMod` homomorfismo inyectivo. Montgomery reduction generica verificada (337 LOC).

### Gaps Identificados

| Gap | Severidad | LOC est. | Blocker |
|-----|-----------|----------|---------|
| CircuitNodeOp sin ops bitwise | CRITICA | 5-10 | Si |
| evalOp sin match cases bitwise | CRITICA | 20-30 | Si |
| SoundRewriteRule inventory bitwise | MEDIA | 200-400 | No |
| ZMod bridges para bitwise | MEDIA | 100-200 | No |
| Cost model para bitwise ops | BAJA | 50-100 | No |
| Field-specific reductions como rules | BAJA | 300-500 | No |

### Extension Points en AMO-Lean

1. **CircuitNodeOp** (`EGraph/Verified/Core.lean:14-22`): Agregar shiftLeft, shiftRight, bitAnd
2. **evalOp** (`EGraph/Verified/SemanticSpec.lean:29-37`): Match cases + nuevos typeclasses
3. **children** (`EGraph/Verified/Core.lean:43-51`): Nuevos constructores
4. **SoundRewriteRule** (`EGraph/Verified/SoundRewriteRule.lean`): Instancias bitwise
5. **NodeOps** (`EGraph/VerifiedExtraction/Core.lean:25-48`): Typeclass generico, ya extensible
6. **localCost** (`EGraph/Verified/Core.lean:61-63`): Modelo de costos para bitwise
7. **toZMod bridges** (`Field/*.lean`): Nuevos lemas para ops bitwise
8. **CircuitExpr** (`VerifiedExtraction/CircuitAdaptor.lean:145-154`): Nuevos constructores de extraccion

---

## 2. Lecciones Aplicables

### Lecciones Reutilizables

| ID | Titulo | Aplicacion | Prioridad |
|----|--------|------------|-----------|
| L-458 | Concrete evalOp vs typeclass NodeSemantics | CircuitNodeOp es CONCRETO, no polimorfic — funcion concreta = menos overhead | CRITICA |
| L-516 | Mirror inductive + tensorReconstruct | Patron de extraccion verificada desde E-graph, reutilizable para bitwise | CRITICA |
| L-016 | Separar prueba: Nat level + ZMod level | Bitwise ops viven en Nat. Probar en Nat primero, luego cast a ZMod | ALTA |
| L-019 | Function.Injective.commRing/field | Bootstrap de Field instances via homomorfismo inyectivo | ALTA |
| L-573 | ZMod patterns (natCast_mod, Fermat) | Lemmas clave para proofs sobre ZMod p | MEDIA |
| L-311 | Three-Part Soundness Contract | Pipeline.sound = fuel + result + frame — para bitwise pipeline | MEDIA |
| L-546 | ConditionalRewriteRule extension | Patron para extender SoundRewriteRule con condiciones campo-especificas | MEDIA |
| L-515 | Option.getD totalizing | Bridge NodeSemantics si evalOp retorna Option | MEDIA |
| L-256 | evalOp_mapChildren law | Ley typeclass esencial para congruencia en E-graph | MEDIA |
| L-353 | omega para aritmetica lineal | Automatizacion para fuel bounds, bit counts | BAJA |

### Anti-patrones a Evitar

| ID | Anti-patron | Impacto |
|----|-------------|---------|
| L-567 | `native_decide` para primes > 2^100 | Compilacion cuelga (>30 min) |
| L-465 | Instanciar NodeSemantics con evalOp que retorna Option | Type mismatch |
| L-478 | Pattern nesting en inductives | Bloquea equation lemmas para TODAS las cases |
| L-614 | Objetivo de igualdad string entre code generators | Fragil, no alcanzable |

---

## 3. Bibliografia Existente Relevante

### Documentos Clave (ya en biblioteca)

| Documento | Carpeta | Relevancia |
|-----------|---------|------------|
| egg (Willsey et al., POPL 2021) | egraphs-treewidth | Fundacion de E-graphs |
| ROVER (Coward et al., 2024) | zk-circuitos | RTL verification via E-graphs |
| Lean-Egg (Rossel et al., POPL 2026) | verificacion | Equality saturation en Lean 4 |
| Fiat-Crypto (Erbsen et al., S&P 2019) | verificacion | Sintesis verificada de aritmetica modular (Coq) |
| Colored E-Graphs (Singher et al., CAV 2023) | verificacion | Conditional rewriting |
| Formally Verified NTT (Trieu, 2025) | ntt, verificacion | Montgomery/Barrett en Rocq |
| E-Graphs as Circuits (Sun et al., 2024) | egraphs-treewidth | Extraction optima via treewidth |
| Guided Equality Saturation (Koehler et al., POPL 2024) | optimizacion | Semi-automatic rewriting |

### Gaps Bibliograficos Cubiertos en Wave 2

| Gap | Paper Descargado |
|-----|------------------|
| CryptOpt | Kuepper et al., PLDI 2023 — verified compilation + randomized search |
| Herbie | Panchekha et al., PLDI 2015 — FP optimization via E-graphs |
| Montgomery 1985 | Original paper — modular multiplication without trial division |
| Barrett 1986 | Original paper — RSA modular reduction on DSP |

---

## 4. Estrategias y Decisiones Previas

### Estrategias Ganadoras

| Estrategia | Proyecto Fuente | Resultado | Aplicacion |
|------------|-----------------|-----------|------------|
| NodeOps typeclass parametrizado | OptiSat v1.3.0 | 363 thms, 0 sorry | BitwiseNodeOp como nueva instancia |
| Bridge 3 capas (types->funcs->props) | AMO-Lean Fases 13-14 | operational<->verified proof | Bitwise Layer 2: shift/and en Nat = field ops |
| ZMod isomorfismo | AMO-Lean N17.1-N17.5 | 0 sorry, 31/64-bit | toZMod bridges para bitwise ops |
| Montgomery addition variant | AMO-Lean N17.3 | 337 LOC, 0 sorry | Reutilizar MU_NEG convention |
| Firewall `_aux` para high-risk proofs | OptiSat/AMO-Lean | 0 sorry mantenido | Para monty_reduce_spec, barrett_correct |
| Rule soundness collection | AMO-Lean Fase 14 | 10 rules en 1-liners | allBitwiseSoundRules pattern |

### Decisiones Arquitecturales Aplicables

1. **Concrete evalOp** (no typeclass) para CircuitNodeOp — simplifica proofs
2. **Two-level proof**: Nat primero (omega, split_ifs), ZMod despues (val_cast_of_lt)
3. **Fuel-based totality**: `match fuel | 0 => base | n+1 => ...` para saturateF
4. **HashMap.fold decomposition**: Probar sobre RESULTADO, no sobre fold directamente

### Benchmarks de Referencia

| Proyecto | LOC | Theorems | Sorry | Build Time |
|----------|-----|----------|-------|------------|
| OptiSat v1.5.2 | 11,310 | 363 | 0 | ~5s |
| AMO-Lean v2.5.1 | ~20,000 | ~500 | 12 (Poseidon) | ~8s |
| VerifiedExtraction v1.0.0 | 2,756 | 203 | 0 | ~2s |
| VeriHE v1.0.0 | ~4,500 | ~150 | 0 | ~4s |
| **Target v3.1.0** | **+2,000-3,000** | **+40-60** | **0** | **~10s** |

### Codigo Reutilizable de Librerias Internas

| Libreria | Path | Que Copiar | Para Que |
|----------|------|------------|----------|
| OptiSat | ~/Documents/claudio/optisat/ | Core.lean (NodeOps), SoundRule.lean | Template E-graph engine |
| VerifiedExtraction | ~/Documents/claudio/VerifiedExtraction/ | Greedy.lean, Integration.lean | Extraction framework |
| AMO-Lean (self) | ./AmoLean/ | BridgeCorrectness.lean, SoundRewriteRule.lean | Rule collection pattern |

---

## 5. Nueva Bibliografia Encontrada

### Papers Descargados (Wave 2)

| Paper | Path | Insight Clave |
|-------|------|---------------|
| CryptOpt (PLDI 2023) | biblioteca/verificacion/kuepper-erbsen-cryptopt-*.pdf | E-graph como **equivalence checker** (no optimizer); sin union-find; canonical ordering |
| Herbie (PLDI 2015) | biblioteca/egraphs-treewidth/panchekha-sanchez-stern-herbie-*.pdf | 3 anti-explosion: scoped simplification, e-class pruning, bounded iterations (~3 iter suficientes) |
| Montgomery (1985) | biblioteca/criptografia/montgomery-modular-multiplication-*.pdf | Hardware REDC = n iteraciones de conditional-add + right-shift-by-1. Invariante: `2^i * S_i = partial_product mod N` |
| Barrett (1986) | biblioteca/criptografia/barrett-implementing-rsa-dsp-*.pdf | 5 ops bitwise: shift, mul reciprocal, mask, subtract, conditional correct. Bound: resultado < 3p, max 2 correcciones |

### Lemmas Mathlib Bitwise Descubiertos (Wave 2)

**CRITICO — Puente Bitwise-Modular:**
- `Nat.and_two_pow_sub_one_eq_mod`: `x &&& (2^n - 1) = x % 2^n`

**testBit (razonamiento bit-level):**
- `Nat.eq_of_testBit_eq` — extensionalidad bitwise
- `Nat.testBit_shiftLeft` / `testBit_shiftRight` — decomposicion de shifts
- `Nat.testBit_and` / `testBit_or` / `testBit_xor` — bitwise ops en testBit
- `Nat.testBit_mod_two_pow` — mod 2^j aisla bits bajos

**AND masking (clave para Montgomery/Barrett):**
- `Nat.and_comm` / `and_assoc` / `and_self` — propiedades algebraicas
- `Nat.and_lt_two_pow` — preservacion de bounds bajo AND

**Shift distribution:**
- `Nat.shiftLeft_and_distrib` / `shiftLeft_or_distrib` / `shiftLeft_xor_distrib`
- `Nat.shiftRight_and_distrib` / `shiftRight_or_distrib` / `shiftRight_xor_distrib`
- `Nat.shiftLeft_add_eq_or_of_lt` — `a <<< i + b = a <<< i ||| b` cuando `b < 2^i`

**Bounds (overflow reasoning):**
- `Nat.or_lt_two_pow` / `xor_lt_two_pow` / `and_lt_two_pow` — ops preservan bounds

---

## 6. Insights de Nueva Bibliografia

### Montgomery 1985 — Descomposicion Hardware de REDC

El REDC hardware procesa un bit por iteracion:
- `S_{i+1} = (S_i + x_i * y [+ N si impar]) / 2`
- Invariante: `2^i * S_i ≡ (x_{i-1}...x_0) * y (mod N)`
- Cada paso = conditional add + right-shift-by-1
- Formalmente: `REDC_step(S, x_i, y, N) = ite(odd(S + x_i*y), (S + x_i*y + N) >>> 1, (S + x_i*y) >>> 1)`
- La variante de "adicion" de AMO-Lean (MU_NEG) corresponde a la observacion de Montgomery de que "one can circumvent overflow by adjusting m so -R < m <= 0"

### Barrett 1986 — Reduccion via Reciprocal

El algoritmo Barrett descompone en 5 operaciones E-graph-nativas:
1. `y = w >>> (n-1) * r` (upper bits * reciprocal)
2. `x = w &&& mask_{n+1} - m * (y >>> (n+1))` (subtract estimate)
3. while `x >= m`: `x -= m` (max 2 correcciones)
- Estadistica: 90% de casos necesitan 0 correcciones, 1% necesita 2
- Branch es altamente predecible (relevante para CPU cost model)

### Herbie 2015 — Tres Mecanismos Anti-Explosion

1. **Scoped simplification**: Solo simplifica hijos de la expresion reescrita, no el grafo completo
2. **E-class pruning**: Cuando una expresion reduce a constante, poda la e-class a solo el literal (operacion destructiva, NO standard en equality saturation)
3. **Bounded iterations**: Formula depth-based; en practica, **3 iteraciones** bastan — "running until saturation does not give better results"
4. **Set Cover pruning**: Maximo 28 programas candidatos de hasta 285 generados

**Aplicacion para AMO-Lean**: `saturateF` ya usa fuel (match con (c)). Estrategias (a) y (b) podrian anadirse como optimizaciones de rendimiento.

### CryptOpt 2023 — E-graph como Equivalence Checker

CryptOpt usa E-graph para **verificar equivalencia**, NO para optimizar:
- Sin union-find merging: "Our domain is simple enough that equalities are discovered at node-creation time"
- Canonical ordering: argumentos commutative ordenados por nombre de variable
- Range analysis: upper bounds en nodos variable controlan aplicacion de reglas
- **Insight**: Para straight-line crypto code (sin control flow), un E-graph simplificado SIN union-find es suficiente
- **Alineacion con Alternativa A**: Confirma que el E-graph como verificador (no descubridor) es la estrategia correcta

### Conexiones Inter-Paper Descubiertas

1. **Barrett reciprocal <-> Montgomery N'**: Ambos requieren precomputacion one-time per modulus; para ZK primes son compile-time constants, haciendo ambos algoritmos puramente bitwise at runtime
2. **CryptOpt E-graph simplificado <-> Herbie bounded E-graph**: Ambos evitan saturacion completa deliberadamente
3. **Montgomery hardware REDC <-> E-graph rewrite step**: Cada paso del REDC es una regla de reescritura condicionada (conditional-add + shift)

---

## 7. Sintesis de Insights

### Hallazgos Clave (Top 10)

1. **El puente bitwise-modular ya existe en Mathlib**: `Nat.and_two_pow_sub_one_eq_mod` (`x &&& (2^n-1) = x % 2^n`) es el lema fundamental. La infraestructura formal esta lista.

2. **CryptOpt confirma la Alternativa A**: E-graph como VERIFICADOR de equivalencia (no optimizador) es exactamente lo que CryptOpt usa en produccion. Sin union-find para straight-line code. AMO-Lean ya tiene la infraestructura completa.

3. **3 iteraciones de saturacion bastan**: Herbie descubrio que saturar mas alla de 3 iteraciones no mejora resultados. Para bitwise field arithmetic (expresiones de 5-10 nodos), esto es mas que suficiente. El `saturateF` existente con fuel=10-20 es sobrado.

4. **Montgomery y Barrett se descomponen en 5-7 operaciones E-graph-nativas**: Cada paso es shift, mask, add, mul, o conditional. El AST extendido con shiftLeft, shiftRight, bitAnd cubre el 100% de las necesidades.

5. **NodeOps typeclass ya es extensible**: `VerifiedExtraction/Core.lean` define `NodeOps` como typeclass generico. Instanciar `BitwiseNodeOp` (con ops bitwise + algebraicas) reutiliza toda la infraestructura de extraction y soundness.

6. **La variante de adicion de AMO-Lean es formalmente correcta**: La convencion MU_NEG de AMO-Lean corresponde exactamente a la observacion de Montgomery 1985 sobre evitar underflow. El `monty_reduce_spec` ya probado es el fundamento.

7. **No hay literatura previa sobre E-graph + bitwise + field arithmetic**: Esto es una **contribucion novel**. Fiat-Crypto usa pipeline tradicional (no E-graphs), CryptOpt usa E-graph pero no equality saturation completa, Herbie trabaja en floating point. La combinacion es unica.

8. **Los 3 campos tienen folding identities triviales**:
   - Mersenne31: `2^31 ≡ 1 (mod p)` → fold = `(x >>> 31) + (x &&& mask)`
   - BabyBear: `2^31 ≡ 2^27 - 1 (mod p)` → fold = `(x >>> 31) * (2^27-1) + (x &&& mask)`
   - Goldilocks: `2^64 ≡ 2^32 - 1 (mod p)` → fold = `(x >>> 64) * (2^32-1) + (x &&& mask)`

9. **El cost model actual (`mulGate=1, resto=0`) es insuficiente pero extensible**: Para bitwise, shifts y ANDs cuestan ~0.3 cycles (pipeline), mientras mul cuesta 1-3 cycles. El framework de `localCost` en `Core.lean` se extiende trivialmente.

10. **80+ lemmas de Mathlib cubren las necesidades**: testBit, AND/OR/XOR, shifts, masks, bounds — todo el razonamiento bitwise nivel Nat tiene soporte formal completo.

### Riesgos Identificados

| Riesgo | Probabilidad | Impacto | Mitigacion |
|--------|-------------|---------|------------|
| Extender CircuitNodeOp rompe proofs existentes | MEDIA | ALTO | Firewall: crear MixedNodeOp separado, bridge via embedding |
| Explosion del E-graph con reglas bitwise | BAJA | MEDIO | Herbie strategy: bounded iterations (fuel=10), scoped simplification |
| Mathlib bitwise lemmas insuficientes | BAJA | MEDIO | Probar lemmas faltantes en BitwiseLean (libreria auxiliar) |
| evalOp typeclasses breaking change | MEDIA | ALTO | Alternativa: evalOp sobre Nat concreto (no typeclasses para bitwise) |
| Barrett/Montgomery proofs intractables | MEDIA | BAJO | Firewall _aux + 3-session time-box; sorry documentado si necesario |

### Recomendaciones para Planificacion

1. **NO extender CircuitNodeOp directamente**: Crear `MixedNodeOp` como nuevo inductive que INCLUYE CircuitNodeOp + bitwise. Embedding function `toMixed : CircuitNodeOp -> MixedNodeOp`. Esto preserva TODOS los 121 teoremas existentes.

2. **evalOp sobre Nat concreto**: NO usar typeclasses (AND, OR, Shift) para Val. En cambio, evaluar bitwise ops directamente sobre `Nat`. Esto evita breaking changes en la firma de evalOp. El razonamiento: en ZK fields, bitwise ops operan sobre la representacion Nat del campo, no sobre el campo abstracto.

3. **Saturacion acotada por defecto**: fuel=10 para reglas bitwise (Herbie demuestra que 3 bastan). Agregar config parameter para override.

4. **Non-vacuity primero**: Para cada regla bitwise, escribir `example` concreto ANTES de la prueba de soundness. Esto detecta errores de especificacion temprano (L-153).

5. **DAG topologico sugerido**:
   ```
   FUNDACIONAL: MixedNodeOp + evalOp + children
   FUNDACIONAL: Bridge theorems (Nat bitwise <-> Nat mod)
   CRITICO: SoundRewriteRule instances (bitwise identities)
   CRITICO: Field-specific folding rules (Mersenne31, BabyBear, Goldilocks)
   PARALELO: MixedExtractSpec (extraction para MixedNodeOp)
   PARALELO: Cost model extension
   HOJA: Integration tests + pipeline soundness extension
   HOJA: Non-vacuity examples
   ```

6. **Benchmark critico: Fiat-Crypto**: Antes de cerrar fase, comparar cobertura y approach con Fiat-Crypto. AMO-Lean no compite en code generation sino en verificacion de equivalencia via E-graph — enfatizar esta diferencia.

### Recursos Prioritarios

1. **Nat.and_two_pow_sub_one_eq_mod** (Mathlib) — el puente fundamental
2. **CryptOpt paper** (Kuepper 2023) — pattern de equivalence checking
3. **Herbie paper** (Panchekha 2015) — anti-explosion mechanisms
4. **Montgomery 1985** — REDC hardware decomposition
5. **AMO-Lean/EGraph/Verified/SoundRewriteRule.lean** — template de reglas

### Deep Analysis

La libreria **BitwiseLean** (creada en Wave 5) formaliza los teoremas fundamentales:

**Grupos tematicos:**
| Grupo | Cantidad | Dificultad Promedio |
|-------|----------|---------------------|
| Split (word splitting) | 4 | easy |
| Bridge (bitwise<->mod) | 6 | easy-medium |
| ZModBridge (ZMod p) | 3 | easy |
| MersenneFold (2^k-1) | 4 | medium |
| PseudoMersenneFold (2^k-c) | 4 | medium |
| Montgomery (REDC) | 3 | medium-hard |
| Barrett (reduction) | 3 | hard |

**Orden de dependencias:**
```
Split ─────┬──> Bridge ───┬──> ZModBridge
           │              ├──> MersenneFold
           │              ├──> PseudoMersenneFold
           │              ├──> Montgomery
           │              └──> Barrett
```

---

## 8. Teoremas Extraidos (Wave 4)

### Por Grupo Tematico

**Split** (4 teoremas):
- `split_nat_eq`: x = (x >>> n) * 2^n + (x &&& (2^n - 1))
- `split_low_lt`: x &&& (2^n - 1) < 2^n
- `split_high_le`: x >>> n <= x / 2^n
- `recombine_eq`: uniqueness de la descomposicion

**Bridge** (6 teoremas):
- `mask_eq_mod`: x &&& (2^n - 1) = x % 2^n (wrapper Mathlib)
- `shiftRight_eq_div_pow`: x >>> n = x / 2^n
- `shiftLeft_eq_mul_pow`: x <<< n = x * 2^n
- `mod_from_split`: x % p = ((x >>> k) * (2^k % p) + (x &&& mask)) % p
- `zmod_shiftLeft`: cast de shift a ZMod
- `zmod_mask`: cast de mask a ZMod

**MersenneFold** (4 teoremas):
- `mersenne_fold_step`: x % (2^k-1) = ((x>>>k) + (x &&&mask)) % (2^k-1)
- `mersenne_fold_bound`: fold result < 2^(k+1)
- `mersenne_fold_normalize`: conditional subtraction gives canonical
- `mersenne31_fold_correct`: instanciacion k=31

**PseudoMersenneFold** (4 teoremas):
- `pseudo_mersenne_fold_step`: x % (2^k-c) = ((x>>>k)*c + (x&&&mask)) % (2^k-c)
- `goldilocks_pow64_mod`: 2^64 % p = 2^32 - 1
- `goldilocks_fold_128`: 128-bit folding
- `babybear_fold_step`: BabyBear-specific

**Montgomery** (3 teoremas):
- `monty_reduce_bitwise_eq`: REDC in bitwise ops
- `monty_reduce_spec`: R * monty_reduce(x) % p = x % p
- `monty_mul_roundtrip`: from_monty(monty_mul(to_monty(a), to_monty(b))) = (a*b) % p

**Barrett** (3 teoremas):
- `barrett_reduce_eq`: Barrett in bitwise ops
- `barrett_reduce_bound`: result < 3p before correction
- `barrett_reduce_correct`: barrett_reduce(x) % p = x % p

### Orden de Dependencias (DAG)

```
split_nat_eq ──> mask_eq_mod ──> mersenne_fold_step ──> mersenne31_fold
split_low_lt ──> shiftRight_eq_div_pow ──> pseudo_mersenne_fold ──> goldilocks_fold_128
               ──> shiftLeft_eq_mul_pow ──> mod_from_split ──> babybear_fold_step
               ──> zmod_shiftLeft        ──> monty_reduce_bitwise_eq ──> monty_reduce_spec
               ──> zmod_mask             ──> barrett_reduce_eq ──> barrett_reduce_correct
```

---

## 9. Formalizacion Lean 4

*(Resultados de Wave 5 — BitwiseLean library)*

### Resumen

| Metrica | Valor |
|---------|-------|
| Archivos creados | 7 + root |
| Teoremas totales | 25 |
| Mathlib | Si (v4.26.0) |
| Toolchain | leanprover/lean4:v4.26.0 |

### Archivos Generados

| Archivo | Teoremas | Descripcion |
|---------|----------|-------------|
| BitwiseLean/Split.lean | 4 | Word splitting at bit boundaries |
| BitwiseLean/Bridge.lean | 6 | Nat bitwise <-> Nat mod bridge |
| BitwiseLean/ZModBridge.lean | 3 | ZMod p bridge for bitwise ops |
| BitwiseLean/MersenneFold.lean | 4 | Mersenne prime folding |
| BitwiseLean/PseudoMersenneFold.lean | 4 | Pseudo-Mersenne folding |
| BitwiseLean/Montgomery.lean | 3 | Montgomery REDC in bitwise terms |
| BitwiseLean/Barrett.lean | 3 | Barrett reduction in bitwise terms |

---

## 10. Libreria Generada

- **Nombre**: BitwiseLean
- **Path**: ~/Documents/claudio/bitwiselean/
- **Mathlib**: Si (v4.26.0)
- **Uso**: Copiar/adaptar teoremas al proyecto AMO-Lean (NUNCA importar como dependencia)

### Teoremas Clave para AMO-Lean v3.1

1. `mask_eq_mod` — puente fundamental para traducir masking a modular arithmetic
2. `mersenne_fold_step` — regla de reescritura para Mersenne31
3. `pseudo_mersenne_fold_step` — regla de reescritura para BabyBear/Goldilocks
4. `monty_reduce_bitwise_eq` — Montgomery en terminos E-graph-nativos
5. `mod_from_split` — teorema general de reduccion via splitting
