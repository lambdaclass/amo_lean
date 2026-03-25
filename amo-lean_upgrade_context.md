# AMO-Lean v2.7 Upgrade Context: Plonky3 Full Certification

**Fecha**: 2026-03-13
**Objetivo**: Certificacion completa de Plonky3 — extension fields, NTT recursivo, FRI verifier completo, MicroC pipeline
**Prerequisito**: Trust-Lean v3.1 (UInt32/UInt64 + bitwise) para la rama MicroC
**Base**: AMO-Lean v2.6.0 (Fase 17 — Plonky3 TV, 3018 LOC, 0 sorry)

---

## 1. Estado actual (v2.6.0)

### Que tenemos

| Componente | Estado | LOC | Teoremas | Sorry |
|------------|--------|-----|----------|-------|
| Mersenne31 Field (p=2^31-1) | COMPLETO | 889 | ~24 | 0 |
| Montgomery Reduction (generico R=2^32) | COMPLETO | 337 | ~18 | 0 |
| Plonky3Field typeclass (3 instancias) | COMPLETO | 180 | ~10 | 0 |
| Mersenne31 Plonky3 TV (from_u62 + refinement) | COMPLETO | 286 | ~15 | 0 |
| BabyBear Montgomery TV (bb_monty_roundtrip) | COMPLETO | 353 | ~29 | 0 |
| Goldilocks Plonky3 TV (algoritmos identicos, rfl) | COMPLETO | 219 | ~10 | 0 |
| NTT Butterfly TV (DIT/DIF sobre PlonkyField) | COMPLETO | 215 | ~8 | 0 |
| FRI Fold TV (fold_step + foldPolynomial bridge) | COMPLETO | 326 | ~14 | 0 |
| Plonky3 TV Pipeline (master theorem) | COMPLETO | 213 | ~8 | 0 |
| E-Graph Verified Engine | COMPLETO | ~5,100 | ~147 | 0 |
| FRI Algebraic Verification | COMPLETO | ~2,840 | ~123 | 0 |
| VerifiedExtraction (generico) | COMPLETO | ~1,476 | ~35 | 0 |
| Trust-Lean Bridge | COMPLETO | 585 | ~32 | 0 |
| FRI Bridges (Domain/Fold/Merkle/Transcript) | COMPLETO | ~1,600 | ~66 | 0 |
| **Total verificado** | | **~14,000+** | **~550+** | **0** |

### Que falta para "certificacion completa de Plonky3"

1. **Extension fields** — Plonky3 usa BabyBear^4 (extension cuartica) para challenges del STARK
2. **NTT recursivo completo** — Solo tenemos butterfly; falta la recursion Cooley-Tukey completa
3. **FRI verifier completo** — Solo tenemos fold; falta query verification (abrir Merkle + check consistency)
4. **MicroC pipeline** — Conectar Trust-Lean v3.1 para verificar el codigo C generado
5. **Constraint extraction** — Extraer AIR constraints de Plonky3 y verificar en Lean

---

## 2. Tareas para v2.7.0

### Tarea A: Extension Fields (Fp2/Fp4) — ~400 LOC

**Prioridad**: MEDIA-ALTA
**Dificultad**: MEDIA
**Dependencias**: Plonky3Field typeclass (v2.6.0 — ya existe)

**Contexto**: Plonky3 usa campos de extension para:
- Challenges del FRI (en Fp4 = BabyBear^4)
- Extension field arithmetic para el STARK prover
- Karatsuba multiplication para Fp2 y Fp4

**Que hacer**:

1. **Fp2 = F[X]/(X^2 - beta)** (~200 LOC):
   ```lean
   structure Fp2 (F : Type) [Field F] where
     c0 : F  -- real part
     c1 : F  -- imaginary part
   ```
   - Operaciones: add (componentwise), mul (Karatsuba: (a+bi)(c+di) = (ac+bd*beta) + (ad+bc)i)
   - `Field (Fp2 F)` instance
   - `Plonky3Field (Fp2 F)` instance con `char = Plonky3Field.char F`
   - `toZMod` composicion: Fp2 → GaloisField (Mathlib)

2. **Fp4 = Fp2[Y]/(Y^2 - gamma)** (~200 LOC):
   - Misma estructura tower: Fp4 = Fp2 × Fp2
   - Karatsuba multiplication
   - `Field` y `Plonky3Field` instances

3. **TV para extension field ops**:
   - Probar que Fp2.mul y Fp4.mul de Plonky3 son correctas
   - Mirror de `plonky3_source/monty-31/src/extension.rs`

**Fuentes a consultar**:
- `verification/plonky3/plonky3_source/monty-31/src/extension.rs` — Plonky3 extension field impl
- `verification/plonky3/plonky3_source/mersenne-31/src/extension.rs` — Mersenne31 extension
- Mathlib `GaloisField` y `AdjoinRoot` — infraestructura algebraica
- `~/Documents/claudio/biblioteca/indices/criptografia/` — papers sobre extension field arithmetic

**Leccion clave**: L-019 (Function.Injective.commRing/field) — mismo patron para Fp2/Fp4

**Riesgo**: MEDIO — Karatsuba multiplication tiene 3 submultiplicaciones, proof surface ~3x del campo base. Pero el patron es conocido.

---

### Tarea B: NTT Recursivo Completo — ~500 LOC

**Prioridad**: ALTA
**Dificultad**: MEDIA
**Dependencias**: ButterflyTV (v2.6.0), PlonkyField typeclass (v2.6.0)

**Contexto**: v2.6.0 verifico el butterfly (kernel del NTT). El NTT recursivo es la composicion:

```
NTT(coeffs, omega) =
  if len(coeffs) == 1: return coeffs
  even = coeffs[0::2]  -- indices pares
  odd  = coeffs[1::2]  -- indices impares
  NTT_even = NTT(even, omega^2)
  NTT_odd  = NTT(odd, omega^2)
  for i in 0..len/2:
    (result[i], result[i+len/2]) = butterfly(NTT_even[i], NTT_odd[i], omega^i)
  return result
```

**Que hacer**:

1. **NTT spec** — Definicion matematica del DFT:
   ```lean
   def ntt_spec (coeffs : List F) (omega : F) : List F :=
     List.ofFn fun i => coeffs.enum.foldl (fun acc (j, c) => acc + c * omega ^ (i * j)) 0
   ```

2. **NTT recursivo** — Cooley-Tukey radix-2 DIT:
   ```lean
   def ntt_recursive (coeffs : List F) (omega : F) (fuel : Nat) : List F := ...
   ```

3. **Correctness** — `ntt_recursive = ntt_spec`:
   - Split even/odd → recurse → butterfly combine
   - Induccion sobre fuel/length
   - Usa `dit_butterfly_correct` de v2.6.0

4. **Inverse NTT** — `intt_recursive` + roundtrip `intt(ntt(x)) = x`

5. **Plonky3 TV** — Probar que la recursion de Plonky3 (DIF, not DIT) es correcta:
   - Plonky3 usa DIF (decimation in frequency) para NTT
   - DIF = top-down butterflies, then recurse on halves
   - Probar: DIF NTT = DIT NTT (ambos computan el mismo DFT)

**Archivos existentes a reusar**:
- `AmoLean/NTT/CooleyTukey.lean` — `NTT_recursive` ya definido (para Goldilocks)
- `AmoLean/NTT/Butterfly.lean` — butterfly generico
- `AmoLean/NTT/Plonky3/ButterflyTV.lean` — butterfly TV (v2.6.0)
- `AmoLean/NTT/Spec.lean` — posible spec existente

**Fuentes a consultar**:
- `AmoLean/NTT/CooleyTukey.lean` — NTT_recursive existente (verificar si es generico sobre PlonkyField)
- `AmoLean/NTT/Goldilocks.lean` — primitiveRoot, twiddle tables
- `verification/plonky3/plonky3_source/dft/` — Plonky3 NTT implementation
- **Trieu, "Formally Verified NTT" (2025, Rocq)** — `~/Documents/claudio/biblioteca/ntt/Formally Verified Number-Theoretic Transform (Trieu, ntt).pdf` — LECTURA OBLIGATORIA: spec + correctness en proof assistant
- **Harvey, "Faster arithmetic for NTT" (2014)** — `~/Documents/claudio/biblioteca/ntt/` — lazy reduction optimization
- **Scott, "Implementation of the NTT"** — `~/Documents/claudio/biblioteca/ntt/` — Montgomery + excess tracking

**Lecciones**:
```bash
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --hybrid "NTT recursive Cooley-Tukey butterfly composition"
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --lesson L-524  # Butterfly decomposition Parseval
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --lesson L-128  # IsWellFormedNTT preconditions
```

**Riesgo**: MEDIO — El NTT recursivo esta bien entendido. El reto es la induccion sobre la estructura recursiva y el manejo de indices (bit-reverse permutation).

---

### Tarea C: FRI Verifier Completo — ~600 LOC

**Prioridad**: ALTA
**Dificultad**: MEDIA-ALTA
**Dependencias**: FoldTV (v2.6.0), MerkleBridge (Fase 13), TranscriptBridge (Fase 13)

**Contexto**: El FRI verifier de Plonky3 tiene 3 fases:
1. **Commit phase**: Prover envia commitments (Merkle roots) de las evaluaciones
2. **Fold phase**: Verifier envia challenges, prover reduce grado iterativamente
3. **Query phase**: Verifier abre paths de Merkle y verifica consistencia con folds

v2.6.0 cubrio la fase 2 (fold). Falta la fase 3 (query).

**Que hacer**:

1. **Query spec** (~200 LOC):
   ```lean
   /-- A FRI query opens a leaf at index i in each round's commitment,
       and verifies consistency with the fold operation. -/
   def verifyQuery (commitments : List MerkleRoot) (openings : List MerklePath)
       (foldChallenges : List F) (queryIndex : Nat) : Bool := ...
   ```

2. **Query soundness** (~200 LOC):
   - Si el prover es honesto: `verifyQuery = true`
   - Si el prover engana: `verifyQuery = true` con probabilidad ≤ ε
   - Usa `Polynomial.card_roots_le_degree` (ya en FRI Fase 12)

3. **FRI verifier completo** (~200 LOC):
   ```lean
   def friVerifier (proof : FRIProof F) (config : FRIConfig) : Bool :=
     -- Check all fold reductions
     fold_check proof config ∧
     -- Check all query openings
     query_check proof config ∧
     -- Check final constant polynomial
     final_check proof config
   ```

4. **Composicion con pipeline existente**:
   - `fri_verifier_soundness` compone `fold_correct` (v2.6) + `query_soundness` (nuevo) + `final_check_correct`
   - Conecta con `fri_pipeline_soundness` de Fase 12

**Archivos existentes a reusar**:
- `AmoLean/FRI/Verified/PerRoundSoundness.lean` — `per_round_soundness` (ya probado)
- `AmoLean/FRI/Verified/VerifierComposition.lean` — `fri_algebraic_guarantees`
- `AmoLean/FRI/Verified/MerkleSpec.lean` — `merkle_verify_correct`
- `AmoLean/FRI/Verified/MerkleBridge.lean` — `merkleBridge_verify_iff`
- `AmoLean/FRI/Plonky3/FoldTV.lean` — fold TV (v2.6.0)

**Fuentes a consultar**:
- `verification/plonky3/plonky3_source/fri/` — Plonky3 FRI implementation
- **Garreta et al. "Simplified Round-by-round Soundness Proof of FRI" (2025)** — ePrint 2025/1993 — El framework algebraico ya implementado en Fase 12
- **BCIKS20 "Proximity Gaps for RS Codes"** — El axioma `proximity_gap_rs` ya documentado
- `AmoLean/FRI/Verified/FRISemanticSpec.lean` — FRIConfig, FRIRoundInvariant

**Lecciones**:
```bash
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --hybrid "FRI query verification Merkle path consistency"
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --hybrid "Merkle bridge verify path soundness"
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --lesson L-311  # Three-part soundness contract
```

**Riesgo**: MEDIO-ALTO — La composicion fold + query + transcript requiere threading del estado Fiat-Shamir a traves de multiples rondas. Ya tenemos los componentes; el reto es la composicion.

---

### Tarea D: MicroC Pipeline Bridge — ~300 LOC

**Prioridad**: MEDIA
**Dificultad**: MEDIA
**Dependencias**: Trust-Lean v3.1 (Tarea 1-4 del trust-lean_upgrade_context.md)

**Contexto**: Una vez que Trust-Lean v3.1 exista con evaluador UInt32/UInt64 + bitwise, necesitamos bridges en AMO-Lean que conecten:

```
MicroC program (e.g., mersenne31_add.c)
  → [evalMicroC_uint32 from Trust-Lean v3.1]
Nat value
  → [bridge theorem]
Mersenne31Field value
  → [existing toZMod]
ZMod p value
```

**Que hacer**:

1. **MicroC programs para field ops** (~100 LOC):
   - `mersenne31_add_prog : MicroCStmt` — mirrors Plonky3's add
   - `mersenne31_mul_prog : MicroCStmt` — mirrors from_u62
   - `babybear_monty_reduce_prog : MicroCStmt` — mirrors monty_reduce
   - Estos son PROGRAMAS MicroC escritos en Lean, no archivos .c

2. **Simulation bridges** (~100 LOC):
   - `mersenne31_add_microc_correct : evalMicroC_uint32 mersenne31_add_prog env = Mersenne31Field.add ...`
   - Usa `stmtToMicroC_correct_uint32` de Trust-Lean v3.1

3. **Composicion end-to-end** (~100 LOC):
   - `microc_to_zmod : evalMicroC_uint32 prog env → ZMod p`
   - Compone simulation (Trust-Lean) + field refinement (v2.6.0) + toZMod (existing)

**Fuentes a consultar**:
- `AmoLean/Bridge/TrustLean.lean` — bridge existente (v2.2.0)
- Trust-Lean v3.1 (cuando exista): `MicroC/EvalUnsigned.lean`, `MicroC/UnsignedSimulation.lean`
- `AmoLean/Field/Plonky3/Mersenne31TV.lean` — specs de referencia

**Nota**: Esta tarea REQUIERE Trust-Lean v3.1. Si Trust-Lean no esta listo, esta tarea se difiere. Las tareas A, B, C son independientes de Trust-Lean.

---

### Tarea E: Constraint Extraction (CertiPlonk integration) — ~400 LOC

**Prioridad**: ALTA (diferenciador competitivo)
**Dificultad**: ALTA
**Dependencias**: PlonkyField (v2.6.0), Extension fields (Tarea A)

**Contexto**: CertiPlonk (Nethermind) ya extrae AIR constraints de Plonky3 a Lean via un symbolic AIR builder. La integracion con AMO-Lean permitiria:

```
Plonky3 AIR constraints (extracted by CertiPlonk)
  → [import into AMO-Lean]
Constraint system over PlonkyField
  → [verify with E-Graph + extraction]
Optimized circuit
  → [fri_pipeline_soundness]
FRI algebraic guarantees
```

**Que hacer**:

1. **Estudiar CertiPlonk** (~0 LOC, investigacion):
   - Clonar https://github.com/NethermindEth/CertiPlonk
   - Entender el formato de exportacion de constraints
   - Identificar que tipos/structures usa

2. **Adaptor CertiPlonk → AMO-Lean** (~200 LOC):
   - Definir `CertiPlonkConstraint` → `AMO-Lean CircuitNodeOp` mapping
   - O mejor: `CertiPlonkConstraint` → `Expr Int` (el formato de SoundRewriteRule)

3. **Constraint verification** (~200 LOC):
   - Para cada constraint extraido: probar que es satisfecho por el witness
   - Usar el E-Graph engine para optimizar
   - Extraer resultado optimizado

**Fuentes a consultar**:
- https://github.com/NethermindEth/CertiPlonk — Constraint extraction tool
- **CertiPlonk paper** (Nethermind 2025) — Metodologia
- **SP1 zk chips FV** (Nethermind 2024) — Per-chip verification methodology
- `AmoLean/EGraph/Verified/SemanticSpec.lean` — CircuitNodeOp, evalOp
- `AmoLean/EGraph/Verified/BridgeCorrectness.lean` — SoundRewriteRule instances

**Riesgo**: ALTO — Depende de la estabilidad del output de CertiPlonk. Si el formato cambia, el adaptor se rompe. Mitigacion: definir un formato intermedio estable.

---

## 3. DAG de dependencias

```
INDEPENDIENTES (pueden empezar ya):
  Tarea A: Extension Fields (Fp2/Fp4)
  Tarea B: NTT Recursivo
  Tarea C: FRI Verifier Completo

DEPENDE DE TRUST-LEAN v3.1:
  Tarea D: MicroC Pipeline Bridge

DEPENDE DE TAREA A + INVESTIGACION:
  Tarea E: Constraint Extraction

COMPOSICION FINAL:
  Tarea F: Full Pipeline Integration
    ← A, B, C, D (opcional), E (opcional)
```

**Camino critico**: B + C → F (NTT + FRI = core Plonky3 verification)
**Paralelo**: A, D, E son independientes entre si

---

## 4. Orden de ejecucion recomendado

### Fase 18: NTT Recursivo + FRI Verifier (core)

```
B68-B75 (est.):
  B71: NTT spec + recursive definition (FUND)
  B72: NTT correctness (CRIT)
  B73: Inverse NTT + roundtrip (CRIT)
  B74: FRI query spec (FUND)
  B75: FRI query soundness (CRIT)
  B76: FRI verifier completo (HOJA)
```

### Fase 19: Extension Fields + Plonky3 NTT TV

```
B77-B80 (est.):
  B77: Fp2 definition + Field instance (FUND)
  B78: Fp4 = Fp2^2 + Field instance (CRIT)
  B79: Plonky3 DIF NTT TV (PAR)
  B80: Integration (HOJA)
```

### Fase 20: MicroC Pipeline (requiere Trust-Lean v3.1)

```
B81-B83 (est.):
  B81: MicroC field op programs (FUND)
  B82: Simulation bridges (CRIT)
  B83: End-to-end composition (HOJA)
```

### Fase 21: CertiPlonk Integration (investigacion-heavy)

```
B84-B86 (est.):
  B84: CertiPlonk study + adaptor (FUND)
  B85: Constraint verification (CRIT)
  B86: Full pipeline (HOJA)
```

---

## 5. Fuentes completas a consultar

### Tier 1 — Lectura obligatoria antes de empezar

| # | Fuente | Relevancia | Path/URL |
|---|--------|------------|----------|
| 1 | **Trieu, "Formally Verified NTT" (2025)** | NTT spec + correctness template | `~/Documents/claudio/biblioteca/ntt/Formally Verified Number-Theoretic Transform (Trieu, ntt).pdf` |
| 2 | **Garreta et al. "Simplified FRI Soundness" (2025)** | FRI round-by-round framework | ePrint 2025/1993 |
| 3 | **CertiPlonk** (Nethermind) | Constraint extraction | https://github.com/NethermindEth/CertiPlonk |
| 4 | **Plonky3 source** | Reference implementation | `verification/plonky3/plonky3_source/` (en repo) |
| 5 | **AMO-Lean v2.6.0 Fase 17 files** | Base para extension | `AmoLean/Field/Plonky3/`, `AmoLean/NTT/Plonky3/`, etc. |

### Tier 2 — Contexto tecnico

| # | Fuente | Relevancia | Path/URL |
|---|--------|------------|----------|
| 6 | **Jasmin/Kyber Episode IV** (Almeida et al., TCHES 2023) | Per-function NTT refinement | `~/Documents/claudio/biblioteca/` (buscar Kyber) |
| 7 | **Fiat-Crypto** (Erbsen et al., S&P 2019) | Verified codegen pipeline | `~/Documents/claudio/biblioteca/verificacion/` |
| 8 | **Montgomery Verified** (Affeldt et al., ITP 2018) | Montgomery formalization | (online) |
| 9 | **Harvey, "Faster arithmetic for NTT" (2014)** | Lazy reduction | `~/Documents/claudio/biblioteca/ntt/` |
| 10 | **Scott, "Implementation of the NTT"** | Montgomery + excess tracking | `~/Documents/claudio/biblioteca/ntt/` |
| 11 | **BCIKS20 "Proximity Gaps for RS Codes"** | FRI proximity gap | (ya axiomatizado en AMO-Lean) |
| 12 | **CompCert** (Leroy, CACM 2009) | Forward simulation | `~/Documents/claudio/biblioteca/indices/verificacion/compcert.md` |

### Tier 3 — Landscape

| # | Fuente | Relevancia |
|---|--------|------------|
| 13 | **ArkLib** | Lean 4 IOP framework — complementario | https://github.com/Verified-zkEVM/ArkLib |
| 14 | **clean/cLean** | Lean 4 ZK DSL — AIR backend | https://github.com/Verified-zkEVM/clean |
| 15 | **SP1-Lean** | 62 RISC-V opcodes verificados | (Succinct) |
| 16 | **risc0-lean4** | BabyBear + NTT ejecutable | https://github.com/risc0/risc0-lean4 |
| 17 | **0xPolygon/goldilocks** | C++ Goldilocks reference | https://github.com/0xPolygon/goldilocks |
| 18 | **ROVER** (2024) | E-graph proof production | https://arxiv.org/html/2406.12421v1 |

### Lecciones relevantes

```bash
# NTT
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --hybrid "NTT recursive Cooley-Tukey correctness"
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --lesson L-524  # Butterfly decomposition
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --lesson L-128  # IsWellFormedNTT

# FRI
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --hybrid "FRI query Merkle verify soundness"
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --lesson L-311  # Three-part contract

# Extension fields
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --hybrid "extension field Fp2 Karatsuba Lean4"
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --lesson L-019  # Injective.commRing/field

# Montgomery
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --hybrid "Montgomery reduction formal verification"

# General
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --lesson L-512  # Three-tier bridge
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --lesson L-532  # Trust boundary = hypothesis
python3 ~/Documents/claudio/lecciones/scripts/query_lessons.py --lesson L-659  # Extension-only architecture
```

---

## 6. Metricas estimadas

| Metrica | Fase 18 | Fase 19 | Fase 20 | Fase 21 | Total |
|---------|---------|---------|---------|---------|-------|
| LOC nuevos | ~1,100 | ~600 | ~300 | ~400 | ~2,400 |
| Archivos nuevos | 5-6 | 3-4 | 2-3 | 2-3 | 12-16 |
| Teoremas nuevos | 30-40 | 20-25 | 10-15 | 10-15 | 70-95 |
| Sorry target | 0 | 0 | 0 | 0 | 0 |
| Axiomas nuevos | 0 | 0 | 0 | 0 | 0 |

**Total v2.7.0**: ~2,400 LOC nuevos, ~80 teoremas, 0 sorry, 0 axiomas
**Total acumulado** (v2.7.0): ~16,400+ LOC verificados, ~630+ teoremas

---

## 7. Criterios de exito para "Plonky3 Full Certification"

| Criterio | Status v2.6 | Target v2.7 |
|----------|-------------|-------------|
| Field arithmetic TV (3 campos) | DONE | DONE |
| Montgomery reduction TV | DONE | DONE |
| Extension field TV (Fp2, Fp4) | — | DONE |
| NTT butterfly TV | DONE | DONE |
| NTT recursivo completo | — | DONE |
| FRI fold TV | DONE | DONE |
| FRI query verification | — | DONE |
| FRI verifier end-to-end | — | DONE |
| MicroC pipeline bridge | — | DONE (si Trust-Lean v3.1 ready) |
| Constraint extraction | — | STARTED (CertiPlonk adaptor) |
| `lake build` clean | DONE | DONE |
| 0 sorry | DONE | DONE |
| 0 custom axioms | DONE (3 crypto std) | DONE (3 crypto std) |
| End-to-end master theorem | `plonky3_tv_complete` | `plonky3_full_certification` |
