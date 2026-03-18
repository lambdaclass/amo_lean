# Insights: AMO-Lean v2.4.1 — Operational-Verified Bridge + SlimCheck

**Fecha**: 2026-02-28
**Dominio**: lean4, formal verification, property-based testing
**Estado del objeto**: upgrade (v2.4.0 has 357 operational FRI defs + 123 verified theorems, no formal connection; 0 SlimCheck in 45K LOC)

## 1. Analisis del Objeto de Estudio

### Resumen

AMO-Lean v2.4.0 tiene **dos mundos paralelos sin puente formal**:
- **Mundo operacional**: 13 archivos FRI (4,916 LOC, ~357 defs) — codigo que ejecuta, genera C, pasa oracle tests
- **Mundo verificado**: 9 archivos FRI/Verified (2,844 LOC, 123 teoremas, 0 sorry) — especificacion con pruebas algebraicas

El gap: no existe ningun teorema que diga "el codigo operacional implementa correctamente la especificacion verificada." Ademas, 0 property tests (SlimCheck) en 45K LOC.

### Inventario Operacional (FRI/)

| Archivo | LOC | Tipos clave | Proposito |
|---------|-----|-------------|-----------|
| CodeGen.lean | 753 | generacion codigo | Rust codegen |
| Merkle.lean | 625 | `FlatMerkle(F,n)`, `MerkleProof(F)` | Merkle flat-array (SIMD) |
| Transcript.lean | 590 | `TranscriptState(F)`, `DomainTag` | Fiat-Shamir sponge |
| Protocol.lean | 574 | `RoundState`, state machine | Protocolo FRI completo |
| Prover.lean | 340 | `ProverState` | Prover iterativo |
| Verifier.lean | 311 | `replayTranscript` | Verificacion estructurada |
| Basic.lean | 303 | `FieldConfig`, `FRIParams` | Tipos core y cost model |
| Proof.lean | 294 | `QueryPoint(F)`, `FRIConfig` | Estructuras query/proof |
| Kernel.lean | 280 | `FRILayerKernel` | IR compilation SIMD |
| Validation.lean | 275 | range checks | Validacion de rangos |
| Fold.lean | 252 | `FRIField`, `friFold` | Fold abstracto type-safe |
| FoldExpr.lean | 197 | expression folding | Operaciones a nivel expr |
| Hash.lean | 122 | `CryptoHash` typeclass | Abstraccion hash |

### Inventario Verificado (FRI/Verified/)

| Archivo | LOC | Teoremas clave | Proposito |
|---------|-----|----------------|-----------|
| FRISemanticSpec.lean | 447 | `FRIEvalDomain`, 3 crypto axioms | Especificacion semantica |
| PerRoundSoundness.lean | 422 | `per_round_soundness` | Garreta 2025 por ronda |
| FoldSoundness.lean | 364 | `fold_preserves_consistency` | Soundness del fold |
| VerifierComposition.lean | 317 | `fri_algebraic_guarantees` | Composicion multi-ronda |
| TranscriptSpec.lean | 279 | `transcript_deterministic` | Fiat-Shamir formal |
| FieldBridge.lean | 266 | `evalOnDomain`, `EvenOddDecomp` | Bridge campo ↔ polinomio |
| MerkleSpec.lean | 258 | `merkle_verify_complete_left` | Merkle tree inductivo |
| FRIPipelineIntegration.lean | 249 | `fri_pipeline_soundness` | Capstone e-graph + FRI |
| BarycentricInterpolation.lean | 238 | `barycentric_eq_lagrange` | NOVEL |

### Type Mismatches Criticos

| Operacional | Verificado | Estado | Bridgeable? |
|-------------|-----------|--------|-------------|
| `FRIField F` (typeclass UInt64) | `[Field F]` (Mathlib) | ✓ Parcial via FieldBridge | Si, toZMod/ofZMod existe |
| `Vec F n` (evaluaciones) | `Polynomial F` (coeficientes) | ⚠️ Parcial via evalOnDomain | Si, pero bijection incompleta |
| `FlatMerkle(F,n)` (flat array) | `MerkleTree F` (inductivo) | ✗ SIN PUENTE | Complejo: index arithmetic |
| `TranscriptState F` (opaco) | `FormalTranscript F` (oracle) | ✗ SIN PUENTE | Medio: estructura similar |
| `friFold` (Vec → Vec) | `foldPolynomial` (Poly → Poly) | ✗ SIN PUENTE | Alto valor si se prueba |
| `CryptoHash.squeeze` | Random Oracle Model axiom | ✓ Axiomatizado | By design (ROM) |

### Keywords

operational-verified bridge, FRI implementation verification, SlimCheck Lean 4, SampleableExt, Shrinkable, Plausible framework, property-based testing proof assistant, FlatMerkle inductive bijection, transcript state formalization, fold polynomial equivalence, type conversion bridge, roundtrip proof, specification mining, Fiat-Shamir operational soundness, ArkLib FRI Lean 4

## 2. Lecciones Aplicables

### Lecciones reutilizables

| ID | Titulo | Aplicacion v2.4.1 |
|----|--------|--------------------|
| L-336 | Bridge Architecture: Type-First with Wrapper Isomorphisms | Probar isomorfismo FlatMerkle↔MerkleTree ANTES de escribir codigo |
| L-368 | Roundtrip Properties as Bridge | friFold → foldPolynomial → friFold roundtrip como puente |
| L-359 | Injectivity via forward roundtrip | toFormal ∘ fromFormal = id para cada tipo bridge |
| L-352 | Spec functions must connect to implementations | Cada def verificada necesita teorema linking a operacional |
| L-146 | Bridge lemma para conectar formas | Crear bridge lemma una vez entre Vec y Polynomial |
| L-306 | Bridge predicate + injectivity | Predicado puente para entornos operacional↔formal |
| L-311 | Three-Part Soundness Contract | fuel + result semantics + frame para bridges |
| L-351 | Example-based verification insufficient | NO validar bridge solo con #eval; necesita induccion |
| L-138 | NUNCA diferir foundational como debt | Probar roundtrip ANTES de escribir downstream |
| L-339 | Integration Tests via rfl not runtime | `example : actual = expected := rfl` en vez de #eval |
| L-403 | Boundary testing multiple points | Fuel=0, fuel=1, fuel grande para bridges iterativos |
| L-415 | Proof-Carrying Data Structures | Bundle data + proof en BridgedFRIResult |
| L-257 | ExtractableSound as standalone Prop | Separar interfaz operacional de obligacion de verificacion |
| L-209 | beq_iff_eq es bridge Bool↔Prop | Para decidable checks en bridges |

### Anti-patrones a evitar

1. **L-138**: Diferir roundtrip proofs como "debt" — si roundtrip falla, todo el bridge colapsa
2. **L-351**: Validar bridge con 8 ejemplos concretos en vez de induccion estructural
3. **L-465**: Forzar typeclass instantiation entre tipos incompatibles (Option vs Val)
4. **L-360**: Usar List.mapM para conversiones spec — causa IH mismatch; usar recursion custom
5. **L-139**: Axiomatizar bugs conocidos como "limitaciones" sin investigar
6. Usar `simp [*]` en proofs finales — siempre `simp only [lista_explicita]`
7. Tratar SlimCheck como sustituto de pruebas formales — es complemento, no reemplazo

## 3. Bibliografia Existente Relevante

### Documentos clave en biblioteca local

| Documento | Carpeta | Relevancia |
|-----------|---------|------------|
| CompCert (Leroy 2016) | verificacion | Patron de semantic preservation con simulation diagrams |
| Fiat-Crypto/Trieu (2025) | ntt/verificacion | Spec → implementation via synthesis, operational correctness |
| Compositional Optimizations CertiCoq (2021) | verificacion | Multi-pass compiler, fuel semantics, logical relations |
| ethSTARK Docs v1.2 | zk-circuitos | FRI commit/query phases, especificacion operacional |
| Block: Concrete Security FRI | criptografia | Parametros concretos, security bounds |
| Proofs Arguments ZK (Thaler) | zk-circuitos | FRI, polynomial commitments, textbook |
| Verified Cairo (Avigad) | zk-circuitos | AIR specs verificadas en Lean 3/4 |
| HEC: Equality Saturation Verification (Yin 2025) | verificacion | E-graph rewriting para equivalencia funcional |

### Gaps bibliograficos

1. **SlimCheck/Plausible en Lean 4** — 0 papers en biblioteca
2. **Bidirectional spec-implementation bridges** — teoria existe pero no para Lean 4
3. **FRI implementation verification** — teoria si, implementacion verificada no
4. **SampleableExt para tipos custom** — solo documentacion API, no papers

## 4. Estrategias y Decisiones Previas

### Estrategias ganadoras

| Estrategia | Proyecto fuente | Resultado |
|-----------|----------------|-----------|
| Two-Layer Bridge (wrapper types + isomorphism) | Trust-Lean v1.2.0 | 26 theorems, 0 sorry, 0 bugs en 1,659 LOC |
| Three-Part Bridge Predicate (scalar + loop + mem) | VR1CS-Lean v1.3.0 | Frame properties = 1-liner via constructor disjointness |
| Denotational Semantics frozen def + homomorphism | VR1CS-Lean v1.3.0 | 101 rules proven via `simp; ring` after 1 homomorphism |
| Post-hoc adversarial testing WITHOUT SlimCheck | Trust-Lean v1.2.0 | 286 property checks via `decide`/`rfl`/`omega` (stronger) |
| Translation Validation Path B (decoupled oracle) | VR1CS + OptiSat | Oracle genera, small verifier checks (TCB minimal) |
| Fuel composition via max (not sum) | Trust-Lean + OptiSat | Sequential composition keeps fuel small |

### Benchmarks de referencia

| Proyecto | LOC | Teoremas | Bridge LOC | Axioms | Sorry |
|----------|-----|----------|------------|--------|-------|
| Trust-Lean v1.2.0 | 7,429 | 312 | ~2,000 | 0 | 0 |
| VR1CS-Lean v1.3.0 | 16,165 | 301 | ~1,200 | 1 | 0 |
| OptiSat v1.2.0 | 8,956 | 248 | ~800 | 0 | 0 |

### Errores evitados

1. **Axiom monoliths**: 1 axiom grande opaco → 4-5 pequeños auditables (VR1CS)
2. **Instance diamonds**: Wrapper types evitan conflictos de typeclass (Trust-Lean)
3. **foldl induction hell**: Recursion explicita >> foldl para correctness proofs (SuperTensor)
4. **Diferir foundational**: Delay injectivity/disjointness → bugs en fases dependientes (SuperTensor)
5. **SlimCheck unavailability as blocker**: Formal proofs (`decide`, `rfl`) son estrictamente MAS FUERTES que random testing (Trust-Lean)

## 5. Nueva Bibliografia Encontrada (Online)

### Papers clave

| Paper | Tipo | Relevancia |
|-------|------|------------|
| Foundational Property-Based Testing (Paraskevopoulou & Hritcu, ITP 2015) | Paper | ALTA — teoria base para PBT dentro de proof assistants |
| Programmable PBT (Keles et al., 2025) | Paper | MEDIA — runners customizados para PBT |
| Fiat-Shamir Security of FRI (Nethermind, Crypto 2023) | Paper | ALTA — base matematica para ArkLib/ArkLibFri |
| QuickChick: PBT in Coq (Software Foundations) | Textbook | ALTA — patrones de diseño transferibles a Lean 4 |
| Using Lean to Verify SP1 (Succinct, 2025) | Blog | MEDIA — operational-to-spec bridge para ZK en Lean 4 |

### Repos clave

| Repo | Organizacion | Relevancia |
|------|-------------|------------|
| **Plausible** | leanprover-community | CRITICA — sucesor moderno de SlimCheck, v0.1.0, Lean 4.26.0, `deriving Arbitrary` |
| **ArkLib** | Verified-zkEVM | ALTA — framework modular SNARK, blueprint FRI en desarrollo |
| **ArkLibFri** | Nethermind | ALTA — FRI formalization, EF-funded, releases mensuales |
| **ZkLinalg** | Math Inc | ALTA — FRI soundness completado (~2K LOC), concrete bounds |
| **LSpec** | Argument Computer | MEDIA — test harness que wrappea SlimCheck/Plausible |

### Hallazgo critico: Plausible

**Plausible** (github.com/leanprover-community/plausible) es el framework moderno de PBT para Lean 4:
- Standalone package (no requiere Mathlib completo)
- Builds on Lean 4.26.0 (nuestro toolchain exacto)
- Soporta `deriving Arbitrary` para ADTs
- `SampleableExt`, `Shrinkable`, `Arbitrary` typeclasses
- `plausible` tactic (sucesor de `slim_check`)
- 82 stars, Apache 2.0, last updated Feb 2026

Pattern para tipos custom:
```lean
-- Auto-derivation para ADTs simples
deriving instance Arbitrary for MySimpleType

-- Manual para tipos con invariantes (e.g., campo finito)
instance : SampleableExt GoldilocksField :=
  SampleableExt.mkSelfContained do
    let n ← SampleableExt.interpSample UInt64
    pure (GoldilocksField.mk (n % GOLDILOCKS_P))
```

## 6. Insights de Nueva Bibliografia

### Insight 1: Plausible > SlimCheck para v2.4.1

Plausible es standalone, compatible con Lean 4.26.0, y tiene `deriving Arbitrary`. Para AMO-Lean:
- Agregar `require plausible from git "..."` en lakefile.lean
- Los tipos simples (Expr, CircuitNodeOp) usan `deriving Arbitrary`
- Los tipos de campo (Goldilocks, BabyBear) necesitan manual `SampleableExt`
- La tactica `plausible` reemplaza `slim_check`

### Insight 2: Formal proofs > random testing (patron Trust-Lean)

Trust-Lean v1.2.0 logro 286 property checks SIN SlimCheck usando `decide`, `rfl`, `omega`. Esto es **estrictamente mas fuerte** que testing aleatorio. Para v2.4.1:
- P0 properties: formal proofs (decide/rfl/omega)
- P1 properties: SlimCheck/Plausible para exploration
- P2 properties: #eval concrete checks

### Insight 3: El bridge Merkle es el mas complejo

`FlatMerkle(F,n)` (flat array, SIMD layout) vs `MerkleTree F` (inductivo) requiere:
1. `flatToInductive : FlatMerkle F n → MerkleTree F` (index arithmetic)
2. `inductiveToFlat : MerkleTree F → FlatMerkle F n`
3. Roundtrip proof: `flatToInductive ∘ inductiveToFlat = id`
4. Hash preservation: `WellFormed hashFn (flatToInductive t)`

Estimacion: 200-300 LOC, 8-12 teoremas. RIESGO MUY ALTO.

### Insight 4: El bridge Transcript es viable pero requiere axioma

`TranscriptState` usa CryptoHash opaco. `FormalTranscript` usa oracle function.
La conexion requiere: "CryptoHash.squeeze se comporta como oracle determinista."
Esto ya esta cubierto por `random_oracle_model` axiom (type True). El bridge es:
```
transcript_bridge : TranscriptState F → FormalTranscript F
  t ↦ { absorbed := t.absorbed, squeezeCount := t.squeezeCount }
```
Si los campos coinciden, el bridge es trivial. Si no, requiere mapping.

### Insight 5: El bridge Fold es el de mayor valor

Probar `friFold xs alpha ≈ foldPolynomial (decompose xs) alpha` conectaria:
- El codigo que ejecuta (Fold.lean, 252 LOC)
- Con la prueba de que fold preserva grado (FoldSoundness.lean, 364 LOC)

Esto convertiria la prueba algebraica abstracta en una garantia sobre codigo real.

### Insight 6: ArkLib planea el mismo bridge pero no lo tiene aun

ArkLib (Verified-zkEVM) explicita que planea "verify functional equivalence of executable specs with Rust implementations." Este bridge operacional-formal es un gap abierto en TODO el ecosistema Lean 4 para ZK. AMO-Lean podria ser el primero en cerrarlo.

## 7. Sintesis de Insights

### Hallazgos clave (Top 10)

1. **Plausible es el framework correcto** — standalone, Lean 4.26.0, `deriving Arbitrary`, reemplaza SlimCheck. Agregar como dependencia en lakefile.lean.

2. **Formal proofs >> random testing** — Trust-Lean demostro 286 checks via `decide`/`rfl` sin SlimCheck. Para bridges, priorizar proofs formales (P0) sobre testing aleatorio (P1).

3. **Three-layer bridge strategy** — Siguiendo Trust-Lean/VR1CS:
   - Layer 1: Type isomorphisms (roundtrip proofs)
   - Layer 2: Function equivalence (operational = spec)
   - Layer 3: Property preservation (invariants transferidos)

4. **Merkle bridge es el gap mas complejo** — FlatMerkle (flat array) vs MerkleTree (inductivo). Requiere index arithmetic correctness. RIESGO MUY ALTO. Considerar axiomatizar si intractable.

5. **Fold bridge tiene el mayor valor** — Conectar `friFold` con `foldPolynomial` convertiria la prueba abstracta en garantia sobre codigo real. Este es EL teorema de mayor impacto.

6. **Transcript bridge es viable** — Si los campos de TranscriptState mapean a FormalTranscript, el bridge es ~50-100 LOC. ROM axiom cubre la semantica.

7. **ArkLib/Nethermind no tiene este bridge aun** — El gap operacional-formal es abierto en todo el ecosistema. AMO-Lean podria ser el primero.

8. **No esperar por SlimCheck** — Usar formal proofs para P0 (soundness) y SlimCheck/Plausible para P1 (exploration). L-351 advierte: examples ≠ proof.

9. **SampleableExt manual para campos** — Goldilocks/BabyBear necesitan instances manuales (modular reduction). Tipos simples (Expr) usan `deriving Arbitrary`.

10. **Estimacion: 1,000-1,500 LOC bridges + 200-300 LOC properties** — ~40-60 nuevos teoremas. Comparable a Trust-Lean bridge effort (~2,000 LOC).

### Riesgos identificados

| Riesgo | Probabilidad | Impacto | Mitigacion |
|--------|-------------|---------|------------|
| FlatMerkle↔MerkleTree index arithmetic intractable | ALTA | ALTO | Axiomatizar flatToInductive si > 3 sesiones |
| friFold↔foldPolynomial type mismatch irreconcilable | MEDIA | MUY ALTO | FieldBridge evalOnDomain como intermediario |
| Plausible incompatible con Mathlib v4.26.0 | BAJA | ALTO | Fallback: usar slim_check de Mathlib directamente |
| SampleableExt para Goldilocks overflow UInt64 | MEDIA | MEDIO | Generar en rango [0, p) con modular reduction |
| Scope creep: intentar bridgear TODO (357 defs) | ALTA | ALTO | Scope a 5 bridges criticos, no 357 |
| ring timeout en proofs de bridge sobre ZMod | MEDIA | MEDIO | Custom simp lemmas, calc steps (L-015) |

### Recomendaciones para planificacion

1. **SCOPE**: Solo 5 bridges criticos, no 357:
   - Fold (friFold ↔ foldPolynomial) — MAYOR VALOR
   - Transcript (TranscriptState ↔ FormalTranscript) — VIABLE
   - Merkle (FlatMerkle ↔ MerkleTree) — RIESGO ALTO, axiomatizar si necesario
   - Query verification (verifyFoldQuery ↔ round soundness) — MEDIO
   - Domain (FRIParams ↔ FRIEvalDomain) — VIABLE

2. **SlimCheck/Plausible**: Agregar ~30 property tests en 3 categorias:
   - Field arithmetic (5): roundtrip, associativity, commutativity
   - FRI operational (15): fold size, Merkle path length, transcript determinism
   - Bridge (10): roundtrip properties entre tipos operacional/verificado

3. **Orden topologico**:
   - B48: Agregar Plausible dependency + SampleableExt instances (FUND)
   - B49: Domain bridge (FRIParams → FRIEvalDomain) (FUND)
   - B50: Transcript bridge (PARALELO con B49)
   - B51: Fold bridge (CRITICO, depende de B49)
   - B52: Merkle bridge o axioma (CRITICO)
   - B53: SlimCheck properties + integration (HOJA)

4. **Metricas target**:
   - ~1,200-1,500 LOC nuevas (bridges + properties)
   - ~40-60 nuevos teoremas
   - 0 sorry, 0-1 engineering axioms
   - ~30 SlimCheck/Plausible properties
   - 5 bridges operacional↔verificado

### Recursos prioritarios (Top 5)

1. **Plausible repo** (github.com/leanprover-community/plausible) — Framework PBT standalone para Lean 4.26.0
2. **Trust-Lean ARCHITECTURE.md** — Patron bridge exitoso (26 theorems, 0 sorry, wrapper isomorphisms)
3. **QuickChick Software Foundations** (softwarefoundations.cis.upenn.edu/qc-current/) — Pedagogia PBT en proof assistant
4. **ArkLib Blueprint** (verified-zkevm.github.io/ArkLib/blueprint/) — Estructura FRI spec en Lean 4
5. **CS2800 SlimCheck Tutorial** (course.ccs.neu.edu/cs2800sp23/l37.html) — Walkthrough SampleableExt manual

### Insights reutilizados de fri_formal_gaps_insights.md (v2.4.0)

Del insights anterior, estos hallazgos siguen vigentes:
- **Insight 1**: Las piezas FRI existen dispersas en Lean 4 — ahora AMO-Lean las tiene internamente
- **Insight 2**: ZkLinalg/ArkLibFri como referencia — siguen relevantes para bridge patterns
- **Insight 5**: Plonky3 prover = TCB — validar outputs, no internals (aplica a bridges)
- **Insight 7**: FRI se descompone en 3 invariantes independientes — los bridges deben respetar esta descomposicion
- **Insight 9**: Precondition audit obligatorio — las bridges heredan precondiciones de ambos mundos

**Para planificar**: `/plan-project 'AMO-Lean v2.4.1 — operational-verified FRI bridges + SlimCheck property testing'`
