# Insights: Cerrar los gaps formales del modulo FRI en AMO-Lean para certificar Plonky3 end-to-end

**Fecha**: 2026-02-27
**Dominio**: lean4, cryptographic formal verification
**Estado del objeto**: upgrade (FRI module exists with 357 defs, 6 trivial theorems; needs ~100+ soundness theorems)

## 1. Analisis del Objeto de Estudio

### Resumen

El modulo FRI en AMO-Lean v2.3.0 consta de 15 archivos Lean (4,916 LOC) con **357 definiciones pero solo 6 teoremas triviales** (3 `True := by trivial` placeholders, 2 `rfl`, 1 type-enforced). Implementa el protocolo FRI completo: fold polynomial, Merkle tree vectorizado, maquina de estados del protocolo, prover, verifier, transcript Fiat-Shamir, y codegen C. Sin embargo, **carece completamente de**:

1. **Soundness formal del fold polinomico** (fold degree preservation, linearity in alpha)
2. **Integridad Merkle** (root uniqueness, membership proof validity, collision resistance)
3. **Fold-polynomial equivalence** (spec vs implementation, barycentric interpolation)
4. **Conexion con el pipeline verificado** (e-graph N11.1-N11.5 + TranslationValidation N11.11)
5. **Verifier soundness** (reject all invalid proofs)
6. **Transcript integrity** (Fiat-Shamir binding, determinism)

### Keywords

FRI soundness, polynomial folding, Merkle tree integrity, interactive oracle proofs, Reed-Solomon proximity, STARK formal verification, Fiat-Shamir formalization, polynomial commitment schemes, ConsistentValuation composition, translation validation, Goldilocks field, BabyBear field, Plonky3 certification, round-by-round soundness, DEEP-FRI

### Gaps Identificados

| Gap | Archivos | Severidad | Descripcion |
|-----|----------|-----------|-------------|
| G1: Fold polynomial equivalence | Fold.lean, FoldExpr.lean | CRITICO | `friFold` sin prueba de preservacion de grado, equivalencia lineal en alpha |
| G2: Merkle tree authentication | Merkle.lean (625 LOC) | CRITICO | Sin root uniqueness, membership validity, collision resistance |
| G3: Fold-Merkle composition | Protocol.lean, Prover.lean | CRITICO | Round transitions sin prueba formal de orden |
| G4: Verifier soundness | Verifier.lean (311 LOC) | ALTA | Sin teorema de rechazo de pruebas invalidas |
| G5: Transcript integrity | Transcript.lean (590 LOC) | ALTA | Sin determinismo robusto ni Fiat-Shamir binding |
| G6: Integration con pipeline | (no existe) | ALTA | Sin conexion formal FRI <-> e-graph pipeline |
| G7: Hash collision model | Hash.lean (122 LOC) | MEDIA | CryptoHash typeclass sin axiomas |

### Dependencias

**Matematicas**: Field theory (Mathlib), polinomios sobre campos finitos, evaluacion/interpolacion, Merkle trees como DAGs, Fiat-Shamir heuristico, complejidad de FRI.

**De AMO-Lean existente**: CircuitEnv + ConsistentValuation (N11.2), CryptoEquivalent (N11.11), Goldilocks/BabyBear (0 axioms), Sigma.Expr + Gather/Scatter, EGraph + extractF (N11.4).

**De librerias internas (copy/adapt)**: ProofKit (foldl/HashMap), VeriHE (depth analysis), OptiSat (TranslationValidation).

## 2. Lecciones Aplicables

### Lecciones reutilizables

| ID | Titulo | Aplicacion FRI |
|----|--------|----------------|
| L-311 | Three-Part Soundness Contract | `full_fri_sound` = (fuel suficiente, evaluacion correcta, frame preservation) |
| L-312 | Zero Sorry Audit as Final Gate | Gate final para certificar 0 axiomas en FRI |
| L-457 | Three-hypothesis CompCert TCB | 3 TCB hypotheses: folding, merkle_integrity, oracle_honest |
| L-415 | Proof-Carrying Data Structures | FRIStep struct con (fold_polynomial, merkle_proof, soundness_proof) |
| L-390 | foldl soundness via List induction | friRounds_soundness via List.foldl_induction sobre rounds |
| L-338 | Fuel Bounds: Compositional via max | FRI fuel bounds para multiples rondas: max, no suma |
| L-146 | Bridge lemma para conectar formas | poly_eval_eq_merkle_fold_equivalence |
| L-329 | Decompose fullBridge into 3 parts | Separar fri_state en (commitment, fold, merkle) invariants |
| L-401 | Strengthening Invariants | merkle_integrity como invariante -> eliminar de firma final |
| L-305 | Nested induction (structural + fuel) | Induccion externa sobre rounds, interna sobre folding iterations |
| L-222 | PostMergeInvariant parcial | PostFoldInvariant para transicion entre rondas FRI |
| L-359 | Injectivity via forward roundtrip | poly_roundtrip: extractFrom . commitTo = id |
| L-351 | Example-based verification insufficient | NO validar soundness solo con ejemplos; induccion obligatoria |
| L-478 | Nested sub-pattern extraction | Helper functions para equation compiler (Perm pattern) |

### Anti-patrones a evitar

- Axiomatizar sin justificacion (L-395, L-402) -> documentar cada axioma en BENCHMARKS.md
- Defer foundational proofs como debt (L-114, L-138) -> probar merkle_integrity ANTES fold_polynomial
- Example-based verification (L-351) -> prueba por induccion sobre estructura de polinomio
- Mezclar representaciones sin bridge (L-43) -> roundtrip explicito merkle<->polynomial
- Atacar teorema principal sin lemas auxiliares -> construir fri_step_correct antes de fri_rounds_correct
- `simp` opaco (L-F9-007) -> siempre `simp only [explicit list]`

## 3. Bibliografia Existente Relevante

### Documentos clave en biblioteca local

| Documento | Carpeta | Relevancia |
|-----------|---------|------------|
| ethSTARK Documentation v1.2 (Ben-Sasson) | criptografia/zk-circuitos | Especificacion completa STARK+FRI, commit/query phases |
| On the Concrete Security of Non-interactive FRI (Block) | criptografia | Seguridad concreta FRI, parametros para SNARKs |
| Aurora: Transparent Succinct Arguments (Chiesa) | criptografia/zk-circuitos | Primer IOP univariante con RS, construccion FRI-based |
| Plonky3 Security Audit Report | verificacion | Auditoria FRI verifier, MMMT commitments, Poseidon2 |
| Formalizing Soundness Proofs of Linear PCP SNARKs (Bailey) | criptografia/zk-circuitos | Formalizacion Lean 3 de Groth'16, tecnicas manipulacion |
| Formally Verified NTT (Trieu) | ntt/verificacion | Rocq NTT formalizado, patron Fiat-Crypto |
| Proofs, Arguments, and Zero-Knowledge (Thaler) | criptografia/zk-circuitos | Textbook IOPs, sumcheck, FRI, polynomial commitments |
| PLONK (Gabizon) | criptografia/zk-circuitos | Polynomial commitments, Lagrange bases |
| Verified Cairo Execution (Avigad/Goldberg) | criptografia/zk-circuitos | AIR encoding verificado en Lean |
| POSEIDON hash function | criptografia | Hash STARK-friendly, sponge construction |

### Gaps bibliograficos (pre-busqueda online)

1. Formalizacion de FRI en CUALQUIER proof assistant
2. Merkle tree con propiedades criptograficas en proof assistants
3. Polynomial commitment soundness formalizado
4. Barycentric interpolation correctness formalizado
5. Fiat-Shamir transform security formalizado para IOPs
6. STARK-to-Plonky3 end-to-end verificacion

## 4. Estrategias y Decisiones Previas

### Estrategias ganadoras

| Estrategia | Proyecto fuente | Resultado |
|-----------|----------------|-----------|
| Two-Level Soundness (Level 1 internal + Level 2 external) | AMO-Lean v2.3.0 | 0 custom axioms, full composition |
| SoundRewriteRule pattern (modular per-operation soundness) | OptiSat v1.2.0 + VR1CS v1.3.0 | 19 rules audited, saturation soundness proven |
| Certificate-Based Verification (verify outputs, not solver) | VR1CS ILP + OptiSat | extractILP_correct, 0 sorry |
| Axiom Elimination: provisional -> constructive -> decidable | AMO-Lean Fase 11 | 9 axioms eliminated |
| Bridge Pattern (roundtrip + injectivity) | AMO-Lean v2.2.0 Trust-Lean | 26 theorems, 0 sorry |
| Precondition Audit GATE | VR1CS N9.4 | Separated 87 unconditional + 14 conditional rules |
| Copy/Adapt Library Patterns, Never Import | CLAUDE.md policy | Zero dependency coupling |

### Decisiones arquitecturales aplicables

1. **Path A (Internal) + Path B (External)**: Dual proof strategy (VR1CS pattern)
   - Path A: FRI semantics fully formal (folding, query, commitment)
   - Path B: Plonky3 output validation (bridge, decidable checks)
2. **Three-Part Contract** (L-311): fuel/bounds + result semantics + frame preservation
3. **Axiom Inventory + TCB Documentation**: Explicit in BENCHMARKS.md
4. **Staged Axiom Elimination**: 3-stage progression per operation

### Benchmarks de referencia

| Proyecto | LOC | Teoremas | Axioms | Sorry | Modelo |
|----------|-----|----------|--------|-------|--------|
| OptiSat v1.2.0 (e-graph universal) | 8,956 | 248 | 0 | 0 | Target density: FRI 40-50% of this |
| AMO-Lean Fase 11 (pipeline) | 1,991 | 77 | 0 | 0 | Similar footprint para FRI |
| VR1CS v1.3.0 (circuit optimizer) | 4,664 | 204 | 0 | 0 | Path A model |

## 5. Nueva Bibliografia Encontrada (Online Research)

### HALLAZGO CRITICO: Ecosistema Lean 4 para ZK Verification

La busqueda online revelo un ecosistema **sorprendentemente rico y activo** de proyectos Lean 4 para verificacion formal de ZK, incluyendo **trabajo directo sobre FRI soundness**:

### Papers Clave Encontrados

| Paper | Autores | Ano | Proof Assistant | Relevancia |
|-------|---------|-----|-----------------|------------|
| **ZkLinalg: FRI soundness in Lean 4** | Math Inc. | 2025 | Lean 4 | **CRITICA** |
| **ArkLib: Modular SNARK verification** | Verified-zkEVM | 2024+ | Lean 4 | **CRITICA** |
| **ArkLibFri: Batched FRI soundness** | Nethermind | 2025+ | Lean 4 | **CRITICA** |
| **VCVio: Forking Lemma + Fiat-Shamir** | Tuma, Hopper | 2024 | Lean 4 | **CRITICA** |
| **CertiPlonk: Plonky3 constraint verification** | Nethermind | 2025 | Lean 4 | **CRITICA** |
| Fiat-Shamir Security of FRI | Attema, Fehr, Klooss | 2023 | Teorico | ALTA |
| Simplified Round-by-round FRI Soundness | Garreta, Mohnblatt, Wagner | 2025 | Teorico | ALTA |
| FRI Summary (Haboeck) | Haboeck (Polygon) | 2022 | Teorico | ALTA |
| DEEP-FRI | Ben-Sasson et al. | 2019 | Teorico | ALTA |
| Proximity Gaps for RS Codes | Ben-Sasson et al. | 2020 | Teorico | ALTA |
| Soundness Notions for IOPs | Block et al. | 2024 | Teorico | ALTA |
| KZG formalization in EasyCrypt | --- | 2025 | EasyCrypt | ALTA |
| Computationally-Sound Symbolic Crypto | --- | 2025 | Lean 4 | MEDIA |
| STIR (FRI successor) | Arnon, Chiesa et al. | 2024 | Teorico | MEDIA |
| WHIR (FRI successor) | Arnon, Chiesa et al. | 2024 | Teorico | MEDIA |
| Verified Cairo Compiler | Avigad et al. | 2023 | Lean 4 | ALTA |
| Merkle Patricia Tree (F*) | Sato et al. | 2021 | F* | MEDIA |

### Repositorios Lean 4 para ZK

| Repo | Organizacion | Descripcion | Relevancia |
|------|-------------|-------------|------------|
| **ZkLinalg** | Math Inc. | FRI soundness theorem, parametros concretos, blueprint | **CRITICA** |
| **ArkLib** | Verified-zkEVM | Framework modular SNARK via oracle reductions | **CRITICA** |
| **ArkLibFri** | Nethermind | FRI batched soundness mecanizado, releases mensuales | **CRITICA** |
| **CertiPlonk** | Nethermind | Extraccion + verificacion constraints Plonky3 | **CRITICA** |
| **VCV-io** | Verified-zkEVM | Oracle computation, forking lemma, Fiat-Shamir | **CRITICA** |
| **risc0-lean4** | RISC Zero | Modelo FRI verification en Lean 4, BabyBear, Merkle | **CRITICA** |
| **formal-proofs** | StarkWare | Cairo CPU semantics + STARK AIR encoding | ALTA |
| **proven-zk** | Reilabs | ZK circuit verification (gnark extraction) | MEDIA |

## 6. Insights de Nueva Bibliografia

### Insight 1: Las piezas para FRI end-to-end verificado YA EXISTEN dispersas

Las componentes necesarias para un pipeline FRI-to-Plonky3 verificado **ya estan implementadas en 4-5 proyectos Lean 4 independientes**:

- **Field arithmetic**: AMO-Lean (Goldilocks, BabyBear, 0 axioms)
- **FRI soundness**: ZkLinalg + ArkLibFri (parametros concretos)
- **Fiat-Shamir**: VCVio (forking lemma + FS transform)
- **Plonky3 constraints**: CertiPlonk (extraccion automatica)
- **E-graph optimization**: AMO-Lean pipeline (0 axioms, verified)

**El valor unico de AMO-Lean seria integrarlas en una cadena coherente**, no reimplementar cada pieza.

### Insight 2: ZkLinalg y ArkLibFri son la referencia directa

ZkLinalg (Math Inc.) tiene un FRI soundness theorem con parametros concretos (error < 2^{-79}). ArkLibFri (Nethermind) trabaja en batched FRI soundness. Ambos son Lean 4. **Antes de escribir una sola linea de prueba FRI, estudiar estos dos repos en detalle.**

### Insight 3: La prueba simplificada de Garreta (2025) es la referencia teorica ideal

El paper "Simplified Round-by-round Soundness Proof of FRI" (ePrint 2025/1993) presenta una prueba via state function que acota la probabilidad de transicion por ronda. Es **directamente formalizable** en Lean 4 y significativamente mas simple que la prueba original de Ben-Sasson.

### Insight 4: Barycentric interpolation es el gap original mas limpio

Ningun proof assistant tiene una formalizacion de barycentric interpolation correctness. Es un componente clave del FRI folding step. Es autocontenido, matematicamente bien definido, y seria una contribucion original.

### Insight 5: Plonky3 prover queda como TCB

Siguiendo el patron VR1CS (verify outputs, not solver internals), el prover de Plonky3 debe quedar como Trusted Computing Base. Lo que se verifica formalmente es:
1. Que los **outputs** (commitments, proofs, evaluations) son correctos
2. Que el **verifier** rechaza todas las pruebas invalidas (soundness)
3. Que la **conexion** FRI <-> e-graph pipeline preserva semantica

### Insight 6: RISC Zero ya tiene un modelo ejecutable de FRI en Lean 4

El repositorio `risc0-lean4` incluye `Zkvm/Seal/Fri.lean` con operaciones de verificacion FRI, Merkle tree operations, y campo BabyBear. No es una formalizacion de soundness, sino un **modelo ejecutable** que puede servir como referencia para las definiciones.

### Insight 7: El paper Attema-Fehr-Klooss (2023) conecta FRI con Fiat-Shamir

Es el primer paper que prueba formalmente la seguridad de FRI bajo Fiat-Shamir, cubriendo FRI, batched FRI, y protocolos tipo Plonk (Plonky2, Redshift, ethSTARK, RISC Zero). Esto es exactamente lo que necesitamos para la fase de Fiat-Shamir -> non-interactive FRI.

## 7. Sintesis de Insights

### Hallazgos clave (Top 10)

1. **Las piezas YA EXISTEN en Lean 4** — ZkLinalg (FRI), ArkLibFri (batched FRI), VCVio (Fiat-Shamir), CertiPlonk (Plonky3). El trabajo de AMO-Lean es **integrar**, no reimplementar desde cero.

2. **Estrategia "adapt, don't import"** — Siguiendo la politica CLAUDE.md, estudiar ZkLinalg/ArkLibFri para extraer patrones y teoremas, adaptarlos al contexto AMO-Lean (Goldilocks/BabyBear fields, e-graph pipeline), sin agregar dependencias.

3. **Two-level architecture funciona para FRI** — Level 1 (FRI semantics: fold correctness, Merkle integrity) + Level 2 (Plonky3 output validation via CryptoEquivalent). Mismo patron exitoso del pipeline e-graph.

4. **Garreta 2025 es la prueba a formalizar** — "Simplified Round-by-round Soundness" es mas simple que Ben-Sasson original y directamente formalizable. Estructura: state function que acota probabilidad por ronda.

5. **Barycentric interpolation = contribucion original** — Gap total en la literatura de formalizacion. Autocontenido, matematicamente limpio. Seria la contribucion mas original de AMO-Lean al ecosistema.

6. **Plonky3 prover = TCB** — Verificar outputs, no internals (patron VR1CS). TCB documentado explicitamente. Decidable checks para commitments, query consistency, evaluation correctness.

7. **FRI soundness se descompone en 3 invariantes independientes** — Siguiendo L-329 y L-222:
   - Commitment invariant (Merkle tree well-formed)
   - Fold invariant (polynomial degree decreasing)
   - Query invariant (evaluations consistent with commitments)

8. **Fuel-based totality para rondas FRI** — Patron L-311 + L-338: `friEvalF state fuel` con fuel = depth bound. Composicion via max, no suma.

9. **Precondition audit obligatorio** — 5 core operations (fold, query_verify, commit, challenge, eval) tienen precondiciones implicitas: field characteristic, degree bounds, extension degree. Formalizarlas como ConditionalSoundRewriteRule.

10. **Metricas realistas: 1,500-2,300 LOC nuevas, 37-67 teoremas, 0-1 axioms** — Basado en benchmarks de OptiSat (8,956 LOC universal) y AMO-Lean pipeline (1,991 LOC). FRI es dominio especifico, menor footprint.

### Riesgos identificados

| Riesgo | Probabilidad | Impacto | Mitigacion |
|--------|-------------|---------|------------|
| ZkLinalg/ArkLibFri incompatibles con AMO-Lean architecture | MEDIA | ALTO | Estudiar repos ANTES de disenar. Adaptar patrones, no copiar verbatim |
| Fold polynomial degree reduction no constructivo | ALTA | ALTO | De-risk con Mathlib.Data.Finsupp. Fallback: axiom documentado |
| Merkle collision resistance requiere axioma criptografico | ALTA | MEDIO | Axioma estandar (collision resistance), documentado como TCB |
| Fiat-Shamir sin modelo formal de Random Oracle | ALTA | MEDIO | Adaptar VCVio (ya formalizado en Lean 4). Axiom OR standard |
| Integracion e-graph <-> FRI requiere nuevos invariantes | ALTA | ALTO | FRIEvaluation wrapper sobre ConsistentValuation, de-risk con sketch |
| Dependencia en Mathlib para polinomios formales | MEDIA | MEDIO | Verificar que Polynomial, RootOfUnity, ZMod disponibles en v4.26.0 |
| Barycentric interpolation intractable en Lean | MEDIA | MEDIO | Fallback: axiom + test vectors. Contribution value remains |
| Scope creep: verificar TODO Plonky3 | ALTA | ALTO | Scope a FRI verification chain. AIR/constraints = siguiente version |

### Recomendaciones para planificacion

1. **INMEDIATO: Estudiar ZkLinalg + ArkLibFri** (~4-8h)
   - Clonar ambos repos, leer estructura, identificar teoremas reusables
   - Evaluar compatibilidad con AMO-Lean field arithmetic
   - Mapear que porcentaje del trabajo ya esta hecho

2. **Fase 12A: FRI SemanticSpec** (~2-3 dias)
   - Adaptar patrones de ZkLinalg para definiciones formales
   - FRI_SemanticSpec.lean: tipos, invariantes, precondiciones
   - Bridge: ConsistentValuation -> FRIEvaluation

3. **Fase 12B: Fold Soundness** (~3-5 dias)
   - Formalizar Garreta 2025 simplified round-by-round proof
   - fold_degree_preservation, fold_linearity
   - De-risk: barycentric interpolation (axiom si intractable)

4. **Fase 12C: Merkle Integrity** (~2-3 dias)
   - Adaptar patrones de risc0-lean4 para definiciones
   - merkle_proof_validity, root_uniqueness
   - Collision resistance = axiom estandar (TCB)

5. **Fase 12D: Verifier Soundness + Fiat-Shamir** (~3-5 dias)
   - Adaptar VCVio para Fiat-Shamir transform
   - fri_verifier_soundness: rechaza pruebas invalidas
   - Transcript integrity

6. **Fase 12E: Integration + Pipeline** (~2-3 dias)
   - Componer FRI con e-graph pipeline (N11.5)
   - CryptoEquivalent extension para FRI
   - full_fri_pipeline_soundness theorem

7. **VERSION v2.4.0** (cierre)
   - Zero sorry audit, TCB documentation
   - BENCHMARKS.md actualizados
   - README.md con FRI verification claims

### Recursos prioritarios (Top 5)

1. **ZkLinalg repo** (github.com/math-inc/ZkLinalg) — FRI soundness theorem en Lean 4, referencia directa
2. **ArkLibFri repo** (github.com/NethermindEth/ArkLibFri) — Batched FRI soundness, releases mensuales
3. **Garreta et al. 2025** (ePrint 2025/1993) — Simplified round-by-round proof, directamente formalizable
4. **VCVio repo** (github.com/Verified-zkEVM/VCV-io) — Fiat-Shamir en Lean 4, forking lemma
5. **Attema-Fehr-Klooss 2023** (ePrint 2023/1071) — FRI + Fiat-Shamir security proof (teorico)

**Para planificar con estos insights**: `/plan-project 'Cerrar gaps FRI en AMO-Lean v2.4.0 — certificar Plonky3 end-to-end'`
