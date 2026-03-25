# Insights: AMO-Lean v2.7 — Plonky3 Full Certification

**Fecha**: 2026-03-13
**Dominio**: lean4
**Estado del objeto**: upgrade (v2.6.0 → v2.7.0)

## 1. Analisis del Objeto de Estudio

### Resumen
AMO-Lean v2.7 es la extension de v2.6.0 (Plonky3 Translation Validation, 3018 LOC, 0 sorry) hacia una certificacion **completa** del prover STARK Plonky3. v2.6.0 cubrio field arithmetic refinement (3 campos, butterfly, fold step). v2.7 agrega: (1) extension fields Fp2/Fp4 para challenges STARK, (2) NTT recursivo completo Cooley-Tukey, (3) FRI verifier end-to-end con query verification, (4) MicroC pipeline bridge via Trust-Lean v3.1, (5) CertiPlonk constraint extraction. Target: ~2,400 LOC nuevos, ~80 teoremas, 0 sorry, 0 axiomas nuevos.

### Keywords
extension field, Fp2, Fp4, Karatsuba, PlonkyField, NTT recursive, Cooley-Tukey, DIT, DIF, bit-reverse permutation, FRI verifier, query verification, Merkle consistency, MicroC pipeline, UInt32, UInt64, Trust-Lean v3.1, constraint extraction, AIR, STARK, CertiPlonk, Montgomery, Mersenne31, BabyBear, Goldilocks, proximity gap, polynomial evaluation, circuit extraction

### Estado
**Upgrade**: Fase 17 (v2.6.0) COMPLETADA. 136 archivos .lean, `lake build` 3140 jobs 0 errores. Version v2.6.0 taggeada. Branch main ready para Fase 18.

### Gaps Identificados
1. **Extension field tower semantics** — Fp2 = F[X]/(X^2 - beta) en Lean 4. Patron Injective.commRing aplicable pero no verificado para towers.
2. **NTT inversion correctness** — INTT recursivo + roundtrip. Manejo de indices inversos, normalizacion 1/N.
3. **FRI query composition** — Threading estado Fiat-Shamir a traves de multiples rondas (commit → fold → query).
4. **MicroC UInt32/UInt64 evaluator** — Trust-Lean v3.1 aun no existe. Bloqueante para Tarea D.
5. **CertiPlonk API stability** — Formato de exportacion de constraints puede cambiar.
6. **Mathlib GaloisField API** — Extension fields en Mathlib: AdjoinRoot vs GaloisField vs directo.

### Dependencias Conceptuales
- Mathlib `ZMod p` (CommRing, Field para p primo) — ya usado en v2.6
- Mathlib `Polynomial` (roots, degree, eval) — ya usado en FRI Fase 12
- Mathlib `AdjoinRoot` / `GaloisField` — NUEVO, necesario para Fp2/Fp4
- AMO-Lean PlonkyField typeclass — ya existe (v2.6.0)
- AMO-Lean FoldBridge / MerkleBridge — ya existen (Fase 13)
- Trust-Lean v3.1 MicroC evaluator — NO existe aun

---

## 2. Lecciones Aplicables

### Lecciones Reutilizables

#### Tarea A: Extension Fields (Fp2/Fp4)

| ID | Titulo | Aplicacion |
|----|--------|------------|
| L-019 | Function.Injective.commRing/field | CommRing/Field para Fp2 via toZMod_inj + homomorphisms |
| L-573 | ZMod patterns: natCast_mod, Fermat | ZMod reasoning para Fp2 modular arithmetic |
| L-567 | native_decide too slow for >32-bit | Fp4 elements son 128-bit logicos — NO native_decide |
| L-198 | UInt32 `%` not `-` for modular reduction | Aplica a representacion de Fp2 elements |
| L-516 | Mirror inductive for specifications | Mirror type para Fp2 extraction del e-graph |

#### Tarea B: NTT Recursivo

| ID | Titulo | Aplicacion |
|----|--------|------------|
| L-659 | Extension-only, non-recursive calls | NTT como composicion de stages, no recursion mutua |
| L-478 | Equation compiler: nested patterns | Butterfly indices necesitan patterns planos |
| L-524 | Butterfly decomposition for Parseval | Split even/odd + sum-of-squares para NTT correctness |
| L-128 | IsWellFormedNTT preconditions | Precondiciones: length power of 2, omega primitive root |
| L-652 | WF recursion equation lemmas | Pattern generalize+cases para NTT recursive |

#### Tarea C: FRI Verifier Completo

| ID | Titulo | Aplicacion |
|----|--------|------------|
| L-536 | SAT oracle as certificate verifier | Plonky3 prover = oracle, Lean verifier = checker |
| L-513 | Compositional end-to-end proofs | fold + query + final = composable stages |
| L-528 | Level-based acyclicity check | Evitar DFS para verificar Merkle paths |
| L-411 | Incremental verification | Probar propiedades estructurales primero, luego constraints |
| L-311 | Three-part soundness contract | Fuel sufficiency + result semantics + frame preservation |

#### Tarea D: MicroC Pipeline

| ID | Titulo | Aplicacion |
|----|--------|------------|
| L-512 | Three-Tier Bridge Architecture | Plonky3 (shell) → MicroC verified (core) → soundness (bridge) |
| L-572 | Three-Tier Bridge: Translation Validation | Constraints equality closes parser→interpreter gap |
| L-626 | MicroC Int64 wraps at operation boundaries | UInt32/UInt64 debe seguir mismo patron |
| L-629 | MicroC fuel mono simpler than Core | No for_ case en MicroC fuel mono |
| L-315 | Three-part bridge predicate | Modular update preservation para MicroC state |

#### Tarea E: Constraint Extraction

| ID | Titulo | Aplicacion |
|----|--------|------------|
| L-554 | Fuel-based extraction per-case helpers | Decompose constraint verification per AIR type |
| L-544 | Constraint graph modeling | Treewidth analysis para constraint structure |

### Anti-patrones a Evitar

| # | Anti-patron | Riesgo |
|---|-------------|--------|
| 1 | `native_decide` en campos >32-bit | Fp4 elements (128-bit logicos) causarian timeout |
| 2 | NTT recursivo via recursion mutua | Duplica complejidad de pruebas vs composicion de stages |
| 3 | DFS para acyclicity en certificates | O(n^2) en peor caso. Usar levels pre-computados |
| 4 | Refactorizar Plonky3 Rust para verificar | Construir specs separadas, bridgear via TV |
| 5 | Nested patterns en butterfly indices | Bloquea equation compiler. Extraer helpers |
| 6 | Identity passes `:= id` en pipeline | Oculta deuda tecnica. Documentar como PENDIENTE |
| 7 | Probar CommRing manualmente | Usar Function.Injective.commRing + 6 homomorphisms |

### Tecnicas Criticas (Top 8)

**1. L-019 Function.Injective.commRing/field** (CRITICA para Fp2/Fp4)
Mathlib tiene `Function.Injective.commRing` y `.field`. Requiere: `toZMod_injective`, `toZMod_zero`, `toZMod_one`, `toZMod_add`, `toZMod_mul`, `toZMod_neg`. Una vez probados estos 6 homomorphisms, CommRing y Field se obtienen "gratis". **Aplicar para Fp2 y Fp4.**

**2. L-513 Compositional End-to-End Proofs** (CRITICA para FRI verifier)
Pipeline decomposition: definir stages como funciones independientes, probar cada una, componer en un teorema end-to-end de ~30 lineas. Aplicar: `fri_verifier = fold_stage ∘ query_stage ∘ final_stage`.

**3. L-512 Three-Tier Bridge** (CRITICA para MicroC pipeline)
Tier 1: Plonky3 ops (untrusted shell). Tier 2: MicroC verified core (total, pure, fuel-based). Tier 3: Bridge composition theorems. Nunca refactorizar Tier 1 — crear Tier 2 paralelo y bridgear.

**4. L-536 External Oracle Pattern** (CRITICA para CertiPlonk)
Plonky3 prover → certificate → Lean verifier. TCB = checker function (Bool, decidable), no el solver. `verifyCertificate : Certificate → Bool` + `verify_sound : verifyCertificate cert = true → property`.

**5. L-659 Extension-only Architecture** (CRITICA para NTT)
Definir NTT como composicion de stages (no recursion mutua): `ntt = stage_k ∘ ... ∘ stage_1 ∘ bit_reverse`. Cada stage aplica butterflies a un stride. Simplifica terminacion y pruebas.

**6. L-478 Flat Pattern Splitting** (IMPORTANTE para butterfly indices)
Extraer sub-patterns a helper functions para que el equation compiler genere splitter lemmas. Sin esto, `simp [fn]` no funciona.

**7. L-128 IsWellFormedNTT** (IMPORTANTE para precondiciones)
NTT requiere: `n = 2^k`, `omega^n = 1`, `omega` primitivo. Empaquetar como precondicion `IsWellFormedNTT` para evitar casos degenerados.

**8. L-311 Three-Part Soundness Contract** (IMPORTANTE para pipeline)
Fuel sufficiency + result semantics + frame preservation. Estructura de todos los teoremas de soundness.

---

## 3. Bibliografia Existente Relevante

### Documentos Clave

#### NTT (Number Theoretic Transform)
| Documento | Carpeta | Relevancia |
|-----------|---------|------------|
| Formally Verified NTT (Trieu, 2025) | ntt/ | **MAXIMA**: NTT verificado en Rocq con Barrett reduction |
| Faster arithmetic for NTT (Harvey, 2014) | ntt/ | Lazy reduction, redundant representation |
| Implementation of the NTT (Scott) | ntt/ | Montgomery + excess tracking, constant-time |
| Extended Harvey butterfly (Bradbury) | ntt/ | Radix-4 optimizations |
| Introduction to NTT (Sengupta, 2025) | ntt/ | Fundamentals: cyclic/negacyclic convolution |
| Implementing NTTs (van der Hoeven, 2024) | ntt/ | SIMD-optimized codelets |

#### FRI & STARK
| Documento | Carpeta | Relevancia |
|-----------|---------|------------|
| Concrete Security of Non-interactive FRI | criptografia/ | Parametros de seguridad concretos |
| Plonky3 Security Audit (Least Authority, 2024) | verificacion/ | FRI verifier, Uni-Stark, fields audit |
| ethSTARK Documentation v1.2 | criptografia/zk-circuitos/ | FRI protocol, AIR constraints, Fiat-Shamir |

#### Extension Fields & Arithmetic
| Documento | Carpeta | Relevancia |
|-----------|---------|------------|
| Skyscraper Hash (Bouvier, 2024) | criptografia/hash-security/ | Montgomery squaring sobre extension fields |
| Fiat-Crypto (Erbsen, 2019) | verificacion/ | Verified field arithmetic, 80 prime fields |

#### Constraint Systems & Verification
| Documento | Carpeta | Relevancia |
|-----------|---------|------------|
| Equality-Based Translation Validator (Stepp, 2011) | egraphs-treewidth/ | E-graphs para validacion de compilador |
| HEC: Equivalence Verification (Yin, 2025) | verificacion/ | E-graphs + MLIR para transformaciones |
| CompCert (Leroy, 2016) | verificacion/ | Forward simulation methodology |
| Cairo proof-producing compiler (Avigad, 2023) | — | STARK encoding → Lean proofs |

### Gaps Bibliograficos
1. **Fp2/Fp4 formalization in Lean 4** — Ninguna referencia local cubre esto especificamente
2. **Recursive NTT correctness proofs in proof assistants** — Solo Trieu (Rocq), nada en Lean 4
3. **FRI query verification formal proofs** — Solo Garreta (algebraico), no implementacion
4. **CertiPlonk paper** — No esta en la biblioteca local (necesita descarga)
5. **ArkLib FRI implementation** — No esta en la biblioteca (referencia online)

---

## 4. Estrategias y Decisiones Previas

### De AMO-Lean v2.6.0 (directamente aplicables)

| Estrategia | Resultado | Aplicacion v2.7 |
|------------|-----------|------------------|
| Vertical Slice First | Mersenne31 end-to-end validado en 889 LOC | Aplicar a Fp2: complete slice before Fp4 |
| Nat-level proof first, lift to ZMod | add_val_eq/mul_val_eq pattern probado | Mismo patron para Fp2 ops |
| Montgomery addition REDC variant | Evita Nat underflow | Reutilizar para MicroC bridge |
| ~80% mechanical replication | BabyBear→Mersenne31 fue mecanico | Mersenne31→Fp2(Mersenne31) sera similar |
| PlonkyField typeclass (not extends) | Evita diamond con Field instances | Extender para Fp2/Fp4 (mismo parametro) |
| `rfl` proofs for identical algorithms | Goldilocks refinements todas rfl | Si NTT recursive ya existe, la TV puede ser rfl |

### De VeriHE (extension field patterns)
- VeriHE tiene infraestructura de polinomios y anillos para FHE
- Patron de tower de anillos (R → R[X]/f(X)) aplicable a Fp2/Fp4
- Noise budget tracking es un patron de bound propagation reutilizable para FRI query bounds

### De VerifiedExtraction (generic extraction patterns)
- `NodeOps` typeclass pattern: 4 operaciones + 4 leyes → instance para cualquier tipo
- `ExtractableSound` per-case decomposition → aplicable a constraint verification per-AIR
- `extractF_correct` composicional → patron para fri_verifier_correct

### De OptiSat (pipeline composition)
- `full_pipeline_soundness` compone saturation + extraction → patron para NTT + FRI
- `TranslationValidation` framework con `CryptoEquivalent` → reutilizable para NTT TV

---

## 5. Investigacion Online

### Hallazgos Clave

#### CertiPlonk (Nethermind)
- **Repo**: https://github.com/NethermindEth/CertiPlonk
- **Enfoque**: Symbolic AIR builder que extrae constraints de Plonky3 a Lean
- **API**: `SymbolicExpression` → `LeanConstraint` pipeline
- **Hallazgo**: Usa Plonky3 fork con instrumented builder. Ya verifico 45 opcodes RV32IM de OpenVM.
- **Relevancia**: MAXIMA para Tarea E — adaptar output format a AMO-Lean CircuitNodeOp
- **Escalabilidad probada**: SP1 constraint extraction (Nethermind) usa mismo framework

#### ArkLibFri (Nethermind) — NUEVO HALLAZGO
- **Repo**: https://github.com/NethermindEth/ArkLibFri
- **Enfoque**: Formalizacion FRI-especifica en Lean 4: round consistency, completeness, round-by-round knowledge soundness
- **Relevancia**: CRITICA para Tarea C — referencia arquitectonica directa para FRI query verification
- **Blueprint**: https://verified-zkevm.github.io/ArkLib/blueprint/index.html

#### p3-hax-lean-fri-pipeline (Runtime Verification) — NUEVO HALLAZGO
- **Repo**: github.com/runtimeverification (referencia)
- **Enfoque**: Verificacion de Plonky3 FRI function usando ArkLib FRI specs + hax extraction
- **Relevancia**: ALTA — pipeline end-to-end Plonky3 FRI verification. Combina hax + ArkLib.
- **Fecha**: Actualizado Feb 2026

#### ArkLib (Verified-zkEVM)
- **Repo**: https://github.com/Verified-zkEVM/ArkLib
- **Estado**: Activo, 174 stars, Sum-Check + Spartan + FRI parcial
- **FRI**: En desarrollo (EF grant), STIR/WHIR incluidos
- **Relevancia**: Referencia arquitectonica para FRI query verification

#### clean/cLean (zkSecurity)
- **Repo**: https://github.com/Verified-zkEVM/clean
- **Estado**: Lean 4 DSL para circuitos ZK, backend Plonky3 en desarrollo
- **Relevancia**: Referencia para constraint DSL, no para verificacion formal

#### risc0-lean4
- **Repo**: https://github.com/risc0/risc0-lean4
- **BabyBear**: NTT ejecutable en Lean 4 con extension field (BabyBear^4)
- **Relevancia**: ALTA — referencia arquitectonica para extension field en Lean 4

#### FFaCiL.lean (Argument Computer)
- **Repo**: https://github.com/argumentcomputer/FFaCiL.lean
- **Estado**: Finite Fields in Lean 4, incluye extension tower
- **Relevancia**: Referencia arquitectonica para tower field construction

#### Mathlib Extension Fields
- `Mathlib.FieldTheory.AdjoinRoot` — `AdjoinRoot f` = F[X]/⟨f⟩, tiene `Field` instance si `f` irreducible
- `Mathlib.FieldTheory.Finite.GaloisField` — `GaloisField p n` = campo con p^n elementos
- `Mathlib.FieldTheory.Tower` — Tower law: `[L:K] * [M:L] = [M:K]`
- **Hallazgo clave**: `AdjoinRoot` es el camino mas directo para Fp2 = F[X]/(X^2 - beta)

#### Plonky3 NTT — CORRECCION CRITICA (Online Agent)
- **Plonky3 usa DIT** (Radix2DitParallel), **NO DIF** como se asumia inicialmente
- AMO-Lean CooleyTukey.lean tambien tiene DIT (`NTT_recursive`)
- **Esto simplifica enormemente la Tarea B**: no hay que probar DIF=DIT, solo generalizar el DIT existente sobre PlonkyField
- Plonky3 soporta multiples backends: `Radix2DitParallel`, `RecursiveDft`, `SmallBatchDft`
- Extension field NTT usa `BinomialExtensionField` para challenges pero NTT se computa sobre campo base

#### Trieu NTT Verified (2025, Rocq)
- NTT verificado end-to-end en Rocq con code synthesis via Fiat-Crypto/Bedrock2
- **Estructura de prueba**: (1) polynomial evaluation spec, (2) butterfly correctness, (3) recursive decomposition, (4) inverse NTT + roundtrip
- **Hallazgo**: La estructura es identica a lo planificado para AMO-Lean. Diferencia: Trieu produce C code via Bedrock2, nosotros via Trust-Lean MicroC.

---

## 6. Estrategias de Proyectos Internos

### AMO-Lean NTT Existente

**CooleyTukey.lean** (283 LOC, 8 declarations):
- `NTT_recursive` ya definido — DIT radix-2 sobre GoldilocksField
- `NTT_recursive_length` probado
- `NTT_recursive_unfold` — unfolding lemma
- `NTT_recursive_getElem_upper/lower` — index access proofs
- `gfVal'` — evaluation function
- **Hallazgo**: Existe la base recursiva pero esta especializada a Goldilocks. Para v2.7, necesitamos generalizarla sobre PlonkyField.

**Butterfly.lean** (174 LOC, 16 declarations):
- `butterfly` generico sobre cualquier campo
- `butterfly_matches_ntt_coeff`, `butterfly_sum`, `butterfly_diff`
- `butterfly_twiddle_one/neg_one`
- **Hallazgo**: El butterfly ya es generico. Solo falta la composicion recursiva.

**NTT/Spec.lean** — Specification del DFT (si existe)
- Verificar si existe `ntt_spec` como polynomial evaluation

### AMO-Lean FRI Existente

**PerRoundSoundness.lean** (422 LOC, 25T):
- `per_round_soundness` — error bound per round
- `RoundGuarantee` — struct con garantias por ronda
- **Hallazgo**: La teoria per-round esta completa. Lo que falta es el QUERY phase.

**VerifierComposition.lean** (317 LOC, 10T):
- `fri_algebraic_guarantees` — degree halving + root counting + uniqueness
- `fri_single_round_correct` — completeness + soundness + uniqueness
- **Hallazgo**: La composicion multi-round ALGEBRAICA esta completa. Lo que falta es la composicion OPERACIONAL (abrir Merkle + check).

**MerkleBridge.lean** (261 LOC):
- `merkleBridge_verify_iff` — verificacion de path ya probada
- **Hallazgo**: El Merkle bridge EXISTE. La query verification lo compone con fold.

**FoldBridge.lean** (272 LOC):
- `foldBridgeEquivalence` — fold operacional = fold polinomial
- **Hallazgo**: El fold bridge EXISTE. La query verification compone fold + Merkle.

### VeriHE Patterns (referencia arquitectonica)

- Tower ring construction: `R → R[X]/f(X)` con `f` irreducible
- Noise budget como bound propagation
- SIMD rotation semantics — no directamente aplicable pero patron de "slot-based operations"

---

## 7. Sintesis de Insights

### Hallazgos Clave (Top 10)

**1. AdjoinRoot es el camino para Fp2/Fp4**
Mathlib tiene `AdjoinRoot f` = F[X]/⟨f⟩ con `Field` instance automatica cuando `f` es irreducible. Para Fp2: `AdjoinRoot (X^2 - beta)` donde `beta` es un no-residuo cuadratico. Esto evita construir la aritmetica manualmente. PERO: la performance computacional de `AdjoinRoot` es mala (no es computable eficientemente). Solucion hibrida: struct `Fp2 = (c0, c1)` con ops manuales + bridge theorem a `AdjoinRoot`.

**2. NTT recursive ya tiene base en CooleyTukey.lean**
`NTT_recursive` existe (283 LOC, DIT radix-2, Goldilocks). Para v2.7: (a) generalizarlo sobre PlonkyField, (b) probar equivalencia DIT = DIF, (c) probar roundtrip NTT ∘ INTT = id. La estructura ya esta.

**3. FRI query verification es composicion de bridges existentes**
MerkleBridge + FoldBridge + TranscriptBridge ya existen (Fase 13). La query verification compone: (a) abrir Merkle path (merkleBridge_verify_iff), (b) verificar consistencia con fold (foldBridgeEquivalence), (c) acumular sobre multiples queries. El reto es la COMPOSICION, no los componentes.

**4. Plonky3 TAMBIEN usa DIT (no DIF como se asumia)**
CORRECCION CRITICA del Online Agent: Plonky3 usa `Radix2DitParallel` (DIT), NO DIF. AMO-Lean CooleyTukey.lean tambien usa DIT. Esto **simplifica enormemente** la Tarea B — no hay que probar equivalencia DIF=DIT. Solo generalizar el `NTT_recursive` existente sobre `PlonkyField` y probar correctness vs `ntt_spec`.

**5. Extension field: struct + bridge, no AdjoinRoot directo**
La estrategia optima para Fp2 es: (a) definir `Fp2 F` como struct con `(c0, c1 : F)`, (b) definir ops manualmente (add componentwise, mul Karatsuba), (c) probar `Field` via `Injective.field` con `toAdjoinRoot : Fp2 F → AdjoinRoot (X^2 - beta)`, (d) probar `Plonky3Field (Fp2 F)`. Esto es computacionalmente eficiente y formalmente correcto.

**6. CertiPlonk produce SymbolicExpression, necesita adaptor a CircuitNodeOp**
CertiPlonk extrae constraints como `SymbolicExpression` (suma, producto, constante). El adaptor a AMO-Lean mapea `SymbolicExpression → Expr Int` (el formato de SoundRewriteRule). Esto es mecanico — mismo patron que Bridge.mkRule en Fase 14.

**7. Trust-Lean v3.1 es bloqueante solo para Tarea D**
Las tareas A (extension fields), B (NTT recursivo), C (FRI verifier) son independientes de Trust-Lean. Solo la Tarea D (MicroC pipeline) requiere Trust-Lean v3.1. Comenzar por A+B+C en paralelo.

**8. risc0-lean4 tiene BabyBear^4 como referencia arquitectonica**
El repo risc0-lean4 implementa BabyBear con extension field (BabyBear^4) ejecutable en Lean. No copiar codigo, pero estudiar: como define la tower, como maneja Karatsuba, como instancia Field.

**9. La estructura de Trieu (Rocq NTT) es identica a nuestro plan**
Trieu 2025: (1) poly eval spec, (2) butterfly correct, (3) recursive decomposition, (4) inverse + roundtrip. Nosotros: (1) ntt_spec, (2) dit_butterfly_correct (v2.6), (3) ntt_recursive_correct (v2.7), (4) intt + roundtrip (v2.7). Misma estructura, diferente proof assistant.

**10. FRI verifier es ~600 LOC porque COMPONE, no re-prueba**
Los componentes existen (fold 326 LOC, Merkle 261 LOC, transcript 242 LOC, per-round 422 LOC). El FRI verifier completo COMPONE estos existentes. El esfuerzo nuevo es la composicion (~200 LOC) + query spec (~200 LOC) + integration tests (~200 LOC).

### Riesgos Identificados

| Riesgo | Severidad | Mitigacion |
|--------|-----------|------------|
| AdjoinRoot computacional lento | MEDIA | Struct Fp2 + bridge theorem (no AdjoinRoot directo) |
| NTT DIT ≠ DIF confusion | BAJA | Probar equivalencia como teorema explicito |
| FRI query composition threading | MEDIA | Descomponer en stages, probar cada uno, componer |
| Trust-Lean v3.1 delay | BAJA | Tareas A/B/C son independientes de Trust-Lean |
| CertiPlonk API inestable | ALTA | Definir formato intermedio estable en AMO-Lean |
| Fp4 = Fp2^2 complejidad de prueba | MEDIA | Fp2 primero (vertical slice), Fp4 despues |
| Bit-reverse permutation proof | MEDIA | Ya existe `Perm.lean` (828 LOC) con permutaciones verificadas |

### Recomendaciones para Planificacion

1. **Vertical slice Fp2 antes de Fp4**: Completar Fp2 end-to-end (struct + ops + Field + PlonkyField) antes de tower a Fp4.
2. **Generalizar NTT_recursive antes de TV**: Hacer NTT_recursive generico sobre PlonkyField, luego probar DIF = DIT.
3. **FRI verifier como composicion**: NO re-probar fold/Merkle/transcript. Componer bridges existentes.
4. **Tareas A/B/C en paralelo**: Independientes entre si y de Trust-Lean.
5. **CertiPlonk como ultima tarea**: Depende de API externa, mayor riesgo de cambio.

### Recursos Prioritarios

| # | Recurso | URL/Path | Aplicacion |
|---|---------|----------|------------|
| 1 | Trieu "Formally Verified NTT" (2026) | https://cic.iacr.org/p/2/4/1 | Estructura de prueba para NTT recursivo |
| 2 | ArkLibFri (Nethermind) | https://github.com/NethermindEth/ArkLibFri | FRI query verification en Lean 4 |
| 3 | ArkLib Blueprint | https://verified-zkevm.github.io/ArkLib/blueprint | OracleReduction abstraction |
| 4 | risc0-lean4 BabyBear^4 | https://github.com/risc0/risc0-lean4 | Extension field + NTT en Lean 4 |
| 5 | CertiPlonk | https://github.com/NethermindEth/CertiPlonk | Constraint extraction Plonky3 → Lean |
| 6 | Garreta FRI Soundness 2025 | https://eprint.iacr.org/2025/1993 | State-function FRI proof |
| 7 | Mathlib AdjoinRoot | Mathlib.RingTheory.AdjoinRoot | API para extension fields |
| 8 | AMO-Lean NTT/CooleyTukey.lean | AmoLean/NTT/ | Base para NTT generico (ya DIT!) |
| 9 | AMO-Lean FRI Verified/ (9 files) | AmoLean/FRI/Verified/ | Componentes FRI verifier |
| 10 | Plonky3 source | verification/plonky3/plonky3_source/ | DIT NTT + FRI + fields |
| 11 | clean/cLean | https://github.com/Verified-zkEVM/clean | FormalCircuit DSL para AIR |
| 12 | Plonky3 Audit (Least Authority) | biblioteca/indices/verificacion/ | FRI verifier + fields audit |

---

## 8. Teoremas Extraidos (Deep Analysis)

### Por grupo tematico

#### Grupo A: Extension Fields (Fp2)

| # | Teorema | Statement informal | Dificultad |
|---|---------|-------------------|------------|
| A1 | `fp2_add_correct` | (a0+a1*i) + (b0+b1*i) = (a0+b0) + (a1+b1)*i | trivial |
| A2 | `fp2_mul_karatsuba` | (a0+a1*i)(b0+b1*i) = (a0*b0 + beta*a1*b1) + ((a0+a1)(b0+b1) - a0*b0 - a1*b1)*i | easy |
| A3 | `fp2_neg_correct` | -(a0+a1*i) = (-a0) + (-a1)*i | trivial |
| A4 | `fp2_inv_correct` | (a0+a1*i)^{-1} = (a0/(a0^2-beta*a1^2)) + (-a1/(a0^2-beta*a1^2))*i | medium |
| A5 | `fp2_toAdjoinRoot_hom` | toAdjoinRoot preserves +, *, 0, 1 | medium |
| A6 | `fp2_toAdjoinRoot_injective` | toAdjoinRoot is injective | medium |
| A7 | `fp2_field_instance` | Fp2 F is a Field | easy (via Injective.field) |
| A8 | `fp2_plonkyField_instance` | Fp2 F is a PlonkyField | easy |

#### Grupo B: Extension Fields (Fp4 = Fp2^2)

| # | Teorema | Statement informal | Dificultad |
|---|---------|-------------------|------------|
| B1 | `fp4_mul_karatsuba` | Tower Karatsuba over Fp2 | medium |
| B2 | `fp4_field_instance` | Fp4 is a Field (via Fp2 tower) | easy |
| B3 | `fp4_plonkyField_instance` | Fp4 is a PlonkyField | easy |

#### Grupo C: NTT Recursivo

| # | Teorema | Statement informal | Dificultad |
|---|---------|-------------------|------------|
| C1 | `ntt_spec_def` | DFT(coeffs, omega)[i] = sum_j(coeffs[j] * omega^(i*j)) | trivial |
| C2 | `ntt_recursive_correct` | NTT_recursive(coeffs, omega) = ntt_spec(coeffs, omega) | hard |
| C3 | `dif_ntt_correct` | DIF_NTT(coeffs, omega) = ntt_spec(coeffs, omega) | hard |
| C4 | `dit_eq_dif` | DIT_NTT = DIF_NTT (via bit-reverse) | medium |
| C5 | `intt_recursive_correct` | INTT(NTT(x)) = x (roundtrip) | hard |
| C6 | `ntt_linearity` | NTT(a*x + b*y) = a*NTT(x) + b*NTT(y) | medium |
| C7 | `ntt_convolution` | NTT(x * y) = NTT(x) . NTT(y) (pointwise) | hard |

#### Grupo D: FRI Verifier

| # | Teorema | Statement informal | Dificultad |
|---|---------|-------------------|------------|
| D1 | `query_open_correct` | Opening Merkle path at index i returns committed value | easy (compose MerkleBridge) |
| D2 | `query_consistency` | Opened values are consistent with fold computation | medium |
| D3 | `multi_query_soundness` | k queries catch cheating with prob >= 1 - (rho + epsilon)^k | medium |
| D4 | `fri_verifier_complete` | Honest prover always passes | medium |
| D5 | `fri_verifier_sound` | Dishonest prover caught with high probability | hard |
| D6 | `fri_full_pipeline` | fri_verifier_sound composes with e-graph pipeline | medium |

#### Grupo E: MicroC Bridge

| # | Teorema | Statement informal | Dificultad |
|---|---------|-------------------|------------|
| E1 | `microc_mersenne31_add_correct` | evalMicroC(add_prog) = field add | medium |
| E2 | `microc_mersenne31_mul_correct` | evalMicroC(mul_prog) = field mul | medium |
| E3 | `microc_monty_reduce_correct` | evalMicroC(monty_prog) = monty_reduce | hard |
| E4 | `microc_to_zmod_composition` | evalMicroC → field op → toZMod = ZMod op | medium |

### Orden de Dependencias

```
A1-A3 (Fp2 basic ops)
  → A4 (Fp2 inverse)
  → A5-A6 (AdjoinRoot bridge)
  → A7 (Field instance)
  → A8 (PlonkyField instance)
  → B1-B3 (Fp4 tower)

C1 (NTT spec)
  → C2 (DIT correct) + C3 (DIF correct)
  → C4 (DIT = DIF)
  → C5 (roundtrip)
  → C6-C7 (properties)

D1 (Merkle open)
  → D2 (query consistency)
  → D3 (multi-query soundness)
  → D4 + D5 (completeness + soundness)
  → D6 (full pipeline)

E1-E2 (basic MicroC) — requires Trust-Lean v3.1
  → E3 (Montgomery MicroC)
  → E4 (composition)
```

### Distribucion de Dificultad

| Dificultad | Count | Porcentaje |
|------------|-------|------------|
| trivial | 4 | 15% |
| easy | 7 | 27% |
| medium | 11 | 42% |
| hard | 4 | 15% |

---

## 9. Formalizacion Lean 4

**Nota**: La formalizacion de estos teoremas se hara DURANTE la implementacion de v2.7, no como pre-trabajo. Este documento sirve como blueprint — cada teorema listado en seccion 8 se convertira en un deliverable de un nodo del DAG.

Los teoremas se escribiran ORIGINALMENTE en AMO-Lean (no copiados de ningun proyecto externo). La referencia arquitectonica de risc0-lean4, ArkLib y FFaCiL se usa solo para informar decisiones de diseno, no para copiar implementaciones.

### Resumen de Viabilidad

| Grupo | Teoremas | Viabilidad | Riesgo principal |
|-------|----------|------------|------------------|
| A (Fp2) | 8 | ALTA | AdjoinRoot bridge puede ser complejo |
| B (Fp4) | 3 | ALTA | Mecanico una vez que Fp2 funciona |
| C (NTT) | 7 | MEDIA-ALTA | NTT recursivo + bit-reverse permutation |
| D (FRI) | 6 | MEDIA | Composicion de bridges existentes |
| E (MicroC) | 4 | MEDIA | Bloqueado por Trust-Lean v3.1 |

---

## Fuentes

### Repositorios
- [Plonky3](https://github.com/Plonky3/Plonky3) — v0.5.0, 37 crates
- [CertiPlonk](https://github.com/NethermindEth/CertiPlonk) — Constraint extraction
- [ArkLib](https://github.com/Verified-zkEVM/ArkLib) — Lean 4 IOP framework
- [clean/cLean](https://github.com/Verified-zkEVM/clean) — Lean 4 circuit DSL
- [risc0-lean4](https://github.com/risc0/risc0-lean4) — BabyBear + NTT
- [FFaCiL.lean](https://github.com/argumentcomputer/FFaCiL.lean) — Finite Fields in Lean
- [0xPolygon/goldilocks](https://github.com/0xPolygon/goldilocks) — C++ Goldilocks
- [ROVER](https://arxiv.org/html/2406.12421v1) — Verified e-graph rewriting

### Papers
- Trieu "Formally Verified NTT" (2025, Rocq)
- Garreta et al. "Simplified FRI Soundness" (2025, ePrint 2025/1993)
- Almeida et al. "Formally Verifying Kyber Episode IV" (TCHES 2023)
- Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic" (S&P 2019)
- Leroy "Formal verification of a realistic compiler" (CACM 2009)
- Avigad et al. "A proof-producing compiler for blockchain applications" (ITP 2023)
- Block & Tiwari "On the Concrete Security of Non-interactive FRI"
- Ben-Sasson et al. "ethSTARK Documentation v1.2" (2023)

### Biblioteca Local
- `~/Documents/claudio/biblioteca/ntt/` — 10 papers NTT
- `~/Documents/claudio/biblioteca/indices/verificacion/` — CompCert, Plonky3 audit, HEC
- `~/Documents/claudio/biblioteca/indices/criptografia/` — FRI security, STARK docs
- `~/Documents/claudio/biblioteca/indices/egraphs-treewidth/` — Equality saturation TV
