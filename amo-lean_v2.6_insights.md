# Insights: Camino 2 — Translation Validation per-function para verificar Plonky3

**Fecha**: 2026-03-13
**Dominio**: lean4
**Estado del objeto**: upgrade (v2.5.1 → v2.6.0)

## 1. Analisis del Objeto de Estudio

### Resumen
El "Camino 2" propone verificar funciones criticas de Plonky3 (Rust) mediante Translation Validation per-function, usando AMO-Lean (equality saturation verificado + FRI algebraico) + Trust-Lean (codegen verificado con MicroC). El pipeline: Plonky3 Rust → traducir a MicroC → probar `evalMicroC(version_MicroC) = evalExpandedSigma(version_AMO-Lean)` → usar bridges existentes para conectar con propiedades algebraicas de FRI.

### Keywords
plonky3, translation-validation, field-arithmetic, goldilocks, babybear, mersenne31, montgomery-reduction, ntt-butterfly, fri-fold, microc, trust-lean, forward-simulation, per-function-refinement, constraint-extraction, sound-rewrite-rule

### Estado
**Upgrade**: AMO-Lean v2.5.1 tiene toda la infraestructura algebraica (FRI, E-Graph, bridges, extraction). Trust-Lean v3.0 tiene MicroC formal con Int64, function calls y roundtrip. Falta: campo finito en MicroC, operaciones bitwise, bridge Plonky3-especifico.

### Gaps Identificados
1. **Trust-Lean no tiene aritmetica modular** (ZMod p) — solo Int64 wrapping
2. **Trust-Lean no tiene operaciones bitwise** (<<, >>, &, |, ^) — necesarias para NTT bit-reverse
3. **No existe especificacion formal de Plonky3** en Lean — hay que crearla
4. **No hay bridge entre operaciones u64/u32 y ZMod p** — refinement gap
5. **SIMD no traducible** a MicroC — hay que usar solo path escalar
6. **Montgomery representation** (BabyBear) no modelada en Trust-Lean

### Dependencias Conceptuales
- Mathlib `ZMod p` (CommRing, Field para p primo)
- AMO-Lean FRI specs (FRISemanticSpec, FoldSoundness, FieldBridge)
- Trust-Lean MicroC (evalMicroC, stmtToMicroC_correct)
- Plonky3 source (field ops, FRI fold, NTT butterflies)

---

## 2. Lecciones Aplicables

### Lecciones Reutilizables

| ID | Titulo | Categoria | Aplicacion Camino 2 |
|----|--------|-----------|---------------------|
| L-572 | Three-Tier Bundle (Shell/Core/Bridge) | Arquitectura | Tier 1: Plonky3 Rust (untrusted) / Tier 2: PlonkySpec Lean (verified) / Tier 3: TV bridge |
| L-512 | Internal vs External Soundness | Arquitectura | Level 1: field arithmetic / Level 2: circuit / Level 3: prover |
| L-311 | Three-Part Soundness Contract | Patron | Fuel sufficiency + result semantics + frame preservation |
| L-655 | Call-free equivalence patterns | Bridge | Per-function refinement para field ops |
| L-368 | Bridge theorems as proof bridges | Bridge | A→C (roundtrip) natural, C→B (algebraic) mechanical |
| L-566 | Decidable-to-Prop lifting | Verificacion | Bool checkers para constraint satisfaction |
| L-536 | External Oracle Pattern | Certificados | Plonky3 prover → certificate → Lean verifier |
| L-531 | ILP Certificate decomposition | Certificados | ValidCertificate = Prop wrapper around Bool check |
| L-532 | Trust boundary = hypothesis, NOT axiom | Seguridad | **CRITICO**: Oracle property como hipotesis explicita, nunca axioma |
| L-201 | BabyBear native_decide rapido (31-bit) | Campo finito | BabyBear: native_decide OK / Goldilocks: zpowMod + Lucas |
| L-567 | native_decide timeout en 64-bit | Campo finito | Goldilocks requiere estrategia alternativa |
| L-478 | Equation compiler blocks on nested patterns | Lean 4 | Extraer helpers para patterns planos |
| L-523 | Namespace adaptation is mechanical | Reutilizacion | OptiSat/TV → Plonky3TV: ~1 bug per 715 LOC |
| L-663 | Lifting lemmas for extraction | Extraccion | Reutilizar VerifiedExtraction patterns |
| L-516 | Mirror inductive for specifications | Especificacion | Copiar ConsistentValuation pattern |
| L-318 | Structural homomorphism patterns | Bridge | Roundtrip proof para AST conversion |
| L-562 | TDCertificate decomposition | Certificados | Treewidth DP certificate checking |
| L-199 | Proof strategies for fields | Campo finito | ring, field_simp, norm_num strategies |

### Anti-patrones a Evitar

| ID | Descripcion | Riesgo para Camino 2 |
|----|-------------|----------------------|
| L-269 | No usar LLM para validar proofs criticas | Usar subagente QA + mechanical checks |
| L-436 | Evitar teoremas tautologicos (P → P, True) | Spec audit obligatorio en cada nodo |
| L-351 | Smoke tests ≠ proofs universales | #eval para validation, simp/induction para universales |
| L-614 | No obsesionarse con roundtrip string exacto | AST equality suficiente, flexibility en pretty-print |

---

## 3. Estado Actual de AMO-Lean (Agent 3)

### Inventario Completo

| Nivel | Archivos | LOC | Teoremas | Sorry | Axiomas |
|-------|----------|-----|----------|-------|---------|
| L1: FRI Algebraic | 9 | 2,840 | 123 | 0 | 3 crypto (True) |
| L2: E-Graph Engine | 7 | 2,457 | 120 | 0 | 0 |
| L3: VerifiedExtraction | 5 | 1,476 | 35 | 0 | 0 |
| L0: Trust-Lean Bridge | 1 | 585 | 32 | 0 | 0 |
| **Total** | **22** | **8,358** | **310+** | **0** | **3 documented** |

### 7 Bridges Verificados

| Bridge | Archivo | LOC | Que Conecta | Teorema Clave |
|--------|---------|-----|-------------|---------------|
| Domain | `DomainBridge.lean` | 337 | FRIParams ↔ FRIEvalDomain | `friParamsToDomain` |
| Fold | `FoldBridge.lean` | 272 | friFold ↔ foldPolynomial | `foldBridgeEquivalence` |
| Merkle | `MerkleBridge.lean` | 261 | FlatMerkle ↔ MerkleTree | `merkleBridge_verify_iff` |
| Transcript | `TranscriptBridge.lean` | 242 | TranscriptState ↔ FormalTranscript | `transcriptBridge_absorb/squeeze` |
| Integration | `BridgeIntegration.lean` | 222 | All 4 composed | `operational_verified_bridge_complete` |
| E-Graph Rules | `BridgeCorrectness.lean` | 236 | Expr Int ↔ CircuitNodeOp | `bridge_complete` (10 instances) |
| Trust-Lean | `Bridge/TrustLean.lean` | 585 | ExpandedSigma ↔ TrustLean.Stmt | `convert_injective`, `verifiedCodeGen` |

### Pipeline Soundness Chain

```
L1: full_pipeline_soundness (e-graph: saturation + extraction)
  ↓ composes with
L2: verified_optimization_pipeline (CryptoEquivalent relation)
  ↓ composes with
L3: fri_pipeline_soundness (FRI algebraic guarantees)
  = end-to-end: user spec → optimized e-graph → FRI proof
```

### Hallazgo Clave: Directorio Plonky3 existente
AMO-Lean ya tiene `verification/plonky3/plonky3_shim/` (con Cargo.toml compilado). Esto indica trabajo previo de shim para Plonky3.

---

## 4. Trust-Lean v3.0 — Analisis Profundo (Agent 1)

### Arquitectura

```
FRONTENDS              CORE IR              BACKENDS
┌──────────────┐  ┌──────────────┐  ┌────────────────┐
│ ArithExpr    │  │              │  │ C Backend      │
│ BoolExpr     ├─→│ Stmt (12ops) ├─→│ Rust Backend   │
│ ImpStmt      │  │ Value        │  │                │
│ ExpandedSigma│  │ Fuel-based   │  │ (future: LLVM) │
└──────────────┘  └──────────────┘  └────────────────┘
```

### Gate Theorems

| Theorem | Statement | Archivo |
|---------|-----------|---------|
| `evalStmt_fuel_mono` | Fuel monotonicity | Core/FuelMono.lean |
| `stmtToMicroC_correct` | IR → MicroC simulation | MicroC/Simulation.lean |
| `evalMicroCBinOp_int64_agree` | Int64 in-range agreement | MicroC/Int64Agreement.lean |
| `stmtToMicroC_correct_withCalls` | Simulation con function calls | MicroC/CallSimulation.lean |
| `master_roundtrip` | parse(print(stmt)) = stmt | MicroC/RoundtripMaster.lean |
| `expandedSigmaToStmt_correct` | ExpandedSigma → Stmt simulation | Bridge/Correctness.lean |

### Cobertura C99

| Feature | Status | Notas |
|---------|--------|-------|
| int64_t arithmetic | OK | Wrapping, two's complement |
| +, -, * | OK | BinOp.add/sub/mul |
| ==, < | OK | Resultado bool |
| &&, \|\| | OK | Evaluacion total (no short-circuit) |
| if/else, while, for | OK | Completo con break/continue |
| Function calls (non-recursive) | OK | v3.0 fresh env |
| Arrays (store/load) | OK | Gather/scatter via bridge |
| Parse/Print roundtrip | OK | Todas las constructores |

### GAPS Criticos para Plonky3

| Gap | Severidad | Solucion Propuesta |
|-----|-----------|-------------------|
| **Aritmetica modular (ZMod p)** | CRITICA | Bridge: `wrapModp(x) = x % p`, axiomas de AMO-Lean |
| **Operaciones bitwise (&, \|, ^, <<, >>)** | ALTA | Extender BinOp + eval + MicroC AST |
| **Type casting int ↔ ZMod p** | MEDIA | Wrappers con bridge theorems |
| **Structs/Records** | MEDIA | Flat tuples o array desugaring |
| **128-bit arithmetic** | MEDIA | Hi/lo splitting o `__uint128_t` |
| **SIMD** | BAJA | Usar solo path escalar |

### Esfuerzo Estimado para Extensiones: ~50h expert work

---

## 5. Plonky3 Source Analysis (Agents 2 + 6)

### Campos Finitos — Resumen

| Campo | Primo | Representacion | Aritmetica | MicroC Complexity |
|-------|-------|----------------|------------|-------------------|
| **Mersenne31** | 2^31 - 1 | Directa (u32) | Fold at bit 31 | **MINIMA** (ideal para empezar) |
| **BabyBear** | 2^31 - 2^27 + 1 | Montgomery (u32) | monty_reduce (u64) | BAJA |
| **Goldilocks** | 2^64 - 2^32 + 1 | Directa (u64) | reduce128 (u128) | MEDIA |

### Operaciones Traducibles Directamente a MicroC

| Prioridad | Operacion | C LOC est. | Notas |
|-----------|-----------|-----------|-------|
| 1 | Goldilocks add | 5 | 2 overflowing adds + branch |
| 2 | Goldilocks sub | 5 | Overflowing sub + branch |
| 3 | Goldilocks mul + reduce128 | 15 | u64*u64→u128, 10-inst reduce |
| 4 | MontyField31 add/sub | 4+4 | u32 con conditional correction |
| 5 | MontyField31 monty_reduce | 8 | Core Montgomery, 5 ops u64 |
| 6 | DIT/DIF Butterfly | 4 | (x+tw*y, x-tw*y) |
| 7 | FRI fold (arity-2) | 20 | 1 ext-mul per row |

### Hallazgo Critico: Polygon Goldilocks C++ Implementation

**[0xPolygon/goldilocks](https://github.com/0xPolygon/goldilocks)** — 82.2% C++, 15.5% CUDA:
- `goldilocks_base_field_scalar.hpp` — scalar add/sub/mul con inline assembly
- `goldilocks_base_field_avx.hpp` — AVX2 vectorizado
- Full NTT implementation (Cooley-Tukey radix-2)
- **Ya resuelve el problema "Rust to C" para el campo mas complejo**

### FRI Fold Formula (Plonky3)

```
f_{i+1}(x^2) = (f_i(x) + f_i(-x))/2 + beta * (f_i(x) - f_i(-x))/(2x)
```

Equivalente:
```
result[i] = (lo + hi).halve() + (lo - hi) * beta * halve_inv_power[i]
```

**Coincide con AMO-Lean's `foldPolynomial`** — el bridge es directo.

### Orden de Verificacion Recomendado (easiest → hardest)

1. Mersenne31 add/sub/mul/reduce (u32, bit masking)
2. BabyBear add/sub (u32, conditional correction)
3. BabyBear monty_reduce + mul (u64)
4. Goldilocks add/sub (u64, carry handling)
5. Goldilocks reduce128 + mul (u128)
6. NTT butterfly (1 mul + 2 add/sub)
7. FRI fold arity-2 (2 add/sub + 1 mul + 1 halve)
8. Inverse operations (GCD or addition chain)
9. Extension field multiplication (Karatsuba)
10. Full NTT + Full FRI verifier

---

## 6. Aeneas/Charon/hax — State of the Art (Agent 4)

### Evaluacion de Herramientas de Traduccion Rust → Lean

| Tool | Lean 4 Support | Plonky3 Viability | Blocker Principal |
|------|----------------|-------------------|-------------------|
| **Aeneas** | Si (most mature) | **LOW** | No SIMD, no unsafe, trait complexity |
| **Charon** | N/A (extraction) | MODERATE (extraccion) | Downstream no puede consumir |
| **hax** | En desarrollo | LOW-MODERATE | Lean backend inmaduro, no SIMD |
| **Eurydice** | N/A (produce C) | VERY LOW | No puede manejar Rust de Plonky3 |
| **rocq-of-rust** | No (solo Rocq) | LOW | No Lean 4 |

### Conclusion Clave
**Ninguna herramienta automatizada puede traducir Plonky3 a Lean actualmente.** Los bloqueadores son fundamentales (SIMD, unsafe, 15+ trait hierarchy). El ecosistema ha convergido en verificar **constraints y protocolos**, no la implementacion Rust.

### Proyectos Directamente Relevantes

| Proyecto | Que Hace | Relevancia |
|----------|----------|------------|
| **CertiPlonk** (Nethermind) | Symbolic AIR builder → Lean constraint extraction | **MAXIMA**: Ya extrae constraints de Plonky3 a Lean |
| **clean/cLean** (zkSecurity) | Lean 4 DSL para circuitos ZK (AIR para Plonky3) | ALTA: Backend Plonky3 en desarrollo |
| **ArkLib** | Lean 4 IOP framework (Sum-Check, FRI, Merkle) | ALTA: Complementario a AMO-Lean |
| **SP1-Lean** (Succinct) | 62 RISC-V opcodes verificados vs Sail spec | MEDIA: Metodologia de constraint extraction |
| **risc0-lean4** | BabyBear + NTT + FRI ejecutable en Lean | MEDIA: BabyBear reference implementation |

---

## 7. Translation Validation Literature (Agent 5)

### Tecnicas Mas Relevantes (ordenadas por impacto)

| # | Tecnica | Referencia | Aplicacion |
|---|---------|-----------|------------|
| 1 | **Constraint Extraction** (CertiPlonk) | Nethermind 2025 | Extraer AIR constraints a Lean via symbolic builder |
| 2 | **Per-function Refinement** (Jasmin/Kyber) | Almeida et al. TCHES 2023 | `f_impl(u64) ≡ f_spec(ZMod p)` function-by-function |
| 3 | **Forward Simulation Composition** (CompCert) | Leroy CACM 2009 | Ya lo tenemos con `full_pipeline_soundness` |
| 4 | **CVC5 Finite Field Tactic** | Ozdemir et al. CAV 2023 | Automatizar pruebas via SMT (CertiPlonk lo usa) |
| 5 | **Proof-Producing Rewriting** (ROVER/egg) | ROVER 2024 | E-graphs + certificados — ya tenemos SoundRewriteRule |
| 6 | **Algebraic Encoding Verification** (StarkWare/Cairo) | Avigad et al. ITP 2023 | STARK encoding → Lean proofs |
| 7 | **Correct-by-Construction CodeGen** (Fiat-Crypto) | Erbsen et al. S&P 2019 | Gold standard, pero requiere reescribir pipeline |

### Papers Clave (Tier 1 — Lectura Obligatoria)

1. **CertiPlonk** — Nethermind 2025 — Constraint extraction Plonky3 → Lean
2. **SP1 zk chips FV** — Nethermind 2024 — Metodologia completa per-chip
3. **Jasmin Kyber Episode IV** — Almeida et al. TCHES 2023 — Template per-function NTT + field
4. **ROVER** — 2024 — E-graph rewriting + proof production (paralelo exacto)
5. **Cairo proof-producing compiler** — Avigad et al. ITP 2023 — Auto-generated soundness theorems

### Papers Clave (Tier 2 — Contexto)

6. CompCert backend (Leroy) — Forward simulation + semantic preservation
7. Fiat-Crypto (Erbsen et al.) — Verified code generation pipeline
8. SMT Finite Fields (CVC5) — Automatizacion de pruebas de campo
9. Montgomery Multiplication Verified (Affeldt et al.) — 96 lemmas template
10. Cairo Algebraic Representation (StarkWare) — STARK encoding in Lean

---

## 8. ZK Formal Verification Landscape (Agent 7)

### 23 Proyectos Activos (2024-2026)

| Proyecto | Proof Assistant | Target | Status |
|----------|----------------|--------|--------|
| ArkLib | Lean 4 | IOPs: Sum-Check, Spartan, FRI, STIR, WHIR | Activo (174 stars) |
| CertiPlonk | Lean 4 | Plonky3 AIR constraints | Funcional |
| clean/cLean | Lean 4 | ZK circuits DSL (AIR, PLONK, R1CS) | Activo (126 stars) |
| zkLean | Lean 4 | ZK circuits (R1CS, lookups, RAM) | Funcional |
| ProvenZK | Lean 4 | gnark circuits (Worldcoin verified) | Produccion |
| risc0-lean4 | Lean 4 | RISC Zero zkVM | Ejecutable |
| SP1-Lean | Lean 4 | SP1 Hypercube (62 opcodes) | Core verificado |
| Halva | Lean 4 | Halo2 constraints (bug en Scroll Keccak) | Produccion |
| StarkWare | Lean 3 | Cairo VM + STARK AIR | Completado |
| Fiat-Crypto | Rocq | Field arithmetic codegen | Produccion (Chrome) |
| NTT Verified (ANSSI) | Rocq | NTT complete + incomplete | Publicado (2026) |
| Garden (Formal Land) | Rocq | ZK circuits via LLZK | En desarrollo |

### ArkLib vs AMO-Lean

| Dimension | ArkLib | AMO-Lean |
|-----------|--------|----------|
| **Enfoque** | Framework generico IOPs (teoria) | E-Graph engine + FRI + campos (practica) |
| **FRI** | En desarrollo (EF grant) | **Completado** (8 archivos, 2,600 LOC, 0 sorry) |
| **E-Graph** | No | **18 archivos, 5,100 LOC, 147 theorems** |
| **Campos verificados** | Via Mathlib | **Goldilocks + BabyBear verificados** |
| **Sorry** | Tiene sorrys | **0 sorry** |

**Conclusion**: AMO-Lean y ArkLib son **complementarios**. ArkLib = teoria IOP. AMO-Lean = practica optimizacion + campos concretos.

### Gaps de la Industria (Oportunidades)

1. **End-to-end STARK prover verification** — nadie lo ha hecho
2. **NTT en Lean 4** — solo existe en Rocq (ANSSI, 2026)
3. **Mersenne31 formal verification** — nadie lo ha hecho
4. **Plonky3 full pipeline** — CertiPlonk solo hace constraints individuales

---

## 9. Lecciones y Patrones Locales (Agent 8)

### 5 Tecnicas Probadas

**1. Three-Level Soundness Composition**
```
Level 1: Internal consistency (saturation + extraction)
  → ConsistentValuation preserved
Level 2: External bridge (circuit semantics alignment)
  → CryptoEquivalent relation
Level 3: Composition (TCB boundary)
  → full_pipeline_soundness
```

**2. Bridge Theorems as Proof Bridges**
```
Dificil: A → B directamente
Solucion: A → C (natural/roundtrip) + C → B (mechanical/algebraic)
Plonky3: output → constraints (roundtrip) → FRI spec (algebraic)
```

**3. Decidable-to-Prop Lifting**
```lean
def checkX : Bool := ... -- fast, evaluatable
theorem checkX_sound : checkX = true → PropX := ... -- soundness
-- Use native_decide for concrete instances
```

**4. External Oracle Pattern**
```lean
-- Plonky3 prover → certificate → Lean verifier
structure ProofCertificate where
  constraints : Array Constraint
  witness : Array FieldElem
  fri_data : FRIProofData

def verifyCertificate (cert : ProofCertificate) : Bool := ...
theorem verify_sound (cert) (h : verifyCertificate cert = true) : ... := ...
```

**5. Namespace Adaptation is Mechanical**
```
OptiSat/TranslationValidation → AMO-Lean/TranslationValidation
  Cambio: solo namespace prefixes
  Defect rate: ~1 bug per 715 LOC
  Tiempo: 1-2 dias vs 2-3 semanas from scratch
```

### Decisiones Arquitecturales Aplicables

| Decision | Origen | Aplicacion Camino 2 |
|----------|--------|---------------------|
| Extension-only architecture | Trust-Lean v3.0 | No refactorizar Plonky3 — crear specs separadas |
| Fuel-based totality | Trust-Lean + AMO-Lean | Explicit Nat bounds para todos los loops |
| Three-tier decomposition | Trust-Lean v3.0 | Shell (Rust IO) + Core (verified) + Bridge |
| SoundRewriteRule audit | AMO-Lean Fase 11 | Auditar precondiciones de todas las constraints |
| Firewall _aux pattern | Trust-Lean + VerifiedExtraction | De-risk theorems complejos con sketch primero |

---

## 10. Sintesis de Insights

### Hallazgos Clave (Top 10)

**1. El FRI fold de Plonky3 coincide con AMO-Lean's `foldPolynomial`**
La formula `f_{i+1}(x^2) = (f_i(x) + f_i(-x))/2 + beta*(f_i(x) - f_i(-x))/(2x)` es identica. El bridge FoldBridge.lean ya prueba la equivalencia operacional-algebraica. Para Plonky3, solo falta una capa adicional de refinement: `u64 ops` → `ZMod p` → `foldPolynomial`.

**2. Polygon Goldilocks C++ implementation resuelve "Rust → C" para el campo mas complejo**
El repo `0xPolygon/goldilocks` tiene implementacion production-grade en C++ con scalar, AVX2, AVX512 y CUDA. Esto es una referencia directa para la traduccion a MicroC del campo mas dificil.

**3. Mersenne31 es el punto de entrada ideal**
p = 2^31-1, representacion directa (no Montgomery), reduccion = shift + add, todo en u32/u64. Es el campo mas simple de Plonky3 y nadie lo ha verificado formalmente. Primera oportunidad de "first in Lean 4".

**4. CertiPlonk ya extrae constraints de Plonky3 a Lean**
Nethermind tiene un fork de Plonky3 con symbolic AIR builder que exporta constraints a Lean. Podriamos reutilizar esta infraestructura para la parte de "constraint extraction" del Camino 2.

**5. Ninguna herramienta automatizada puede traducir Plonky3 Rust a Lean**
Aeneas, hax, Eurydice — todas fallan en los traits complejos (15+), SIMD, unsafe. La estrategia de Translation Validation manual (Camino 2) es la unica viable a corto plazo.

**6. El patron Jasmin/Kyber es directamente aplicable**
El paper de Kyber verifico NTT con refinement per-function: `f_spec(F_q)` vs `f_impl(int16)` con bridge de Barrett/Montgomery. Mismo patron para: `goldilocks_mul_spec(ZMod p)` vs `goldilocks_mul_impl(UInt64)`.

**7. AMO-Lean tiene toda la infraestructura algebraica necesaria**
310+ teoremas, 0 sorry, 7 bridges probados. Lo que falta es la capa de refinement `u64/u32 ↔ ZMod p` y la formalizacion de las operaciones concretas de Plonky3.

**8. Trust-Lean necesita extensiones focalizadas (~50h)**
Bitwise ops + ZMod p axioms + type casting son los gaps principales. Las extensiones son modulares (no rompen v3.0).

**9. BabyBear es native_decide-friendly, Goldilocks no**
BabyBear (31-bit): `native_decide` rapido para proofs computacionales. Goldilocks (64-bit): requiere `zpowMod` + Lucas (lento). Esto afecta la estrategia de prueba.

**10. El ecosistema converge en verificar constraints + protocolos, no Rust**
Los proyectos exitosos (CertiPlonk, SP1-Lean, Halva) verifican propiedades matematicas de las constraints, no la implementacion Rust. El Camino 2 es ambicioso porque va mas alla — verifica la *implementacion*.

### Riesgos Identificados

| Riesgo | Severidad | Mitigacion |
|--------|-----------|------------|
| Trust-Lean extension breaks existing proofs | BAJA | Extension-only architecture (nuevos archivos) |
| Plonky3 fold usa algoritmo incompatible | BAJA | Verificado: formula identica a AMO-Lean |
| 128-bit arithmetic en MicroC | MEDIA | Hi/lo splitting o `__uint128_t` GCC extension |
| Montgomery refinement complejo | MEDIA | 96 lemmas de Affeldt et al. como template |
| Goldilocks native_decide timeout | MEDIA | Usar zpowMod + Lucas (ya probado en AMO-Lean) |
| Scope creep (verificar todo Plonky3) | ALTA | Foco en field ops + FRI fold + NTT butterfly |

### Recomendaciones para Planificacion

**Estrategia Recomendada: Vertical Slice First**

En lugar de extender Trust-Lean horizontalmente y luego verificar, hacer un "vertical slice" completo para UNA funcion:

```
Mersenne31::mul (Rust, ~5 LOC)
  → mersenne31_mul_microc (MicroC, ~5 LOC)
  → evalMicroC(mersenne31_mul_microc) = mersenne31_mul_spec(ZMod p)  [Lean theorem]
  → mersenne31_mul_spec = field multiplication in ZMod (2^31 - 1)  [Mathlib]
```

Esto valida la arquitectura end-to-end antes de escalar.

**Fases Propuestas:**

| Fase | Contenido | LOC est. | Semanas |
|------|-----------|----------|---------|
| A | Field Arithmetic Refinement (Mersenne31 → BabyBear → Goldilocks) | ~200 Lean + ~50 C | 2-3 |
| B | Trust-Lean Extensions (bitwise, ZMod p, casting) | ~150 Lean | 1-2 |
| C | NTT Butterfly Verification | ~100 Lean + ~20 C | 1-2 |
| D | FRI Fold Verification | ~300 Lean + ~30 C | 2-3 |
| E | End-to-End Pipeline Integration | ~200 Lean | 1-2 |
| **Total** | | **~950 Lean + ~100 C** | **7-12** |

**Pipeline Recomendado:**

```
Plonky3 (Rust) ───────────────────────────────────────────────┐
  │                                                            │
  │ [Manual translation, per-function]                         │
  ↓                                                            │
MicroC (formal C subset) ← Trust-Lean v3.0+                   │
  │                                                            │
  │ [stmtToMicroC_correct]                                     │
  ↓                                                            │
Trust-Lean Core IR (Stmt)                                      │
  │                                                            │
  │ [expandedSigmaToStmt_correct]                              │
  ↓                                                            │
AMO-Lean ExpandedSigma                                         │
  │                                                            │
  │ [verified_optimization_pipeline]                            │
  ↓                                                            │
E-Graph Verified (full_pipeline_soundness)                     │
  │                                                            │
  │ [fri_pipeline_soundness]                                    │
  ↓                                                            │
FRI Algebraic Spec ←──────── field refinement bridge ──────────┘
  │                         u64/u32 ↔ ZMod p
  │
  ↓
Soundness Guarantees (3 crypto axioms)
```

### Recursos Prioritarios

1. **[0xPolygon/goldilocks](https://github.com/0xPolygon/goldilocks)** — C++ implementation, reference para traduccion
2. **[CertiPlonk](https://github.com/NethermindEth/CertiPlonk)** — Constraint extraction de Plonky3 a Lean
3. **[Jasmin Kyber Episode IV](https://cryptojedi.org/papers/hakyber-20230424.pdf)** — Template per-function refinement
4. **[Affeldt et al. Montgomery Verified](https://link.springer.com/chapter/10.1007/978-3-319-96142-2_30)** — 96 lemmas para Montgomery
5. **[AMO-Lean FRI/Verified/](AmoLean/FRI/Verified/)** — 9 archivos, toda la base algebraica

### Ventaja Competitiva

AMO-Lean es el **unico proyecto** que combina:
- **Verified E-Graph engine** (otros verifican constraints estaticos, no optimizacion)
- **FRI algebraic verification** completa (ArkLib aun en desarrollo)
- **Campos finitos concretos verificados** (Goldilocks + BabyBear en Lean 4)
- **Trust-Lean codegen bridge** (pipeline Lean → C verificado)
- **0 sorry, 0 custom axioms** (solo 3 standard crypto axioms)

La pieza que falta es el **refinement bridge** entre operaciones de maquina (u64/u32) y especificaciones algebraicas (ZMod p). El Camino 2 llena este gap.

---

## Fuentes

### Repositorios
- [Plonky3](https://github.com/Plonky3/Plonky3) — v0.5.0, 37 crates
- [Polygon Goldilocks C++](https://github.com/0xPolygon/goldilocks) — Production scalar + SIMD + CUDA
- [CertiPlonk](https://github.com/NethermindEth/CertiPlonk) — Constraint extraction Plonky3 → Lean
- [ArkLib](https://github.com/Verified-zkEVM/ArkLib) — Lean 4 IOP framework
- [clean/cLean](https://github.com/Verified-zkEVM/clean) — Lean 4 circuit DSL
- [Aeneas](https://github.com/AeneasVerif/aeneas) — Rust → Lean translation
- [Charon](https://github.com/AeneasVerif/charon) — Rust MIR extraction
- [hax](https://github.com/hacspec/hax) — Rust → F*/Lean extraction
- [ROVER](https://arxiv.org/html/2406.12421v1) — Verified e-graph rewriting
- [FFaCiL](https://github.com/argumentcomputer/FFaCiL.lean) — Finite Fields in Lean
- [risc0-lean4](https://github.com/risc0/risc0-lean4) — BabyBear + NTT in Lean

### Papers
- Almeida et al. "Formally Verifying Kyber Episode IV" (TCHES 2023)
- Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic" (S&P 2019)
- Affeldt et al. "Formally Verified Montgomery Multiplication" (ITP 2018)
- Leroy "Formal verification of a realistic compiler" (CACM 2009)
- Avigad et al. "A proof-producing compiler for blockchain applications" (ITP 2023)
- Ozdemir et al. "Satisfiability Modulo Finite Fields" (CAV 2023)
- Trieu "Formally Verified NTT" (CiC 2026)
- ePrint 2025/1700 "Computationally-Sound Symbolic Cryptography in Lean"
