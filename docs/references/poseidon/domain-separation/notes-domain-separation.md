# Notas: Domain Separation para Poseidon2 + FRI

**Fecha**: 2026-01-27
**Propósito**: Análisis de bibliografía para Step 5.2 - Auditoría de Domain Separation
**Documentos analizados**: 9 papers/especificaciones

---

## Resumen Ejecutivo

Domain separation es una técnica criptográfica que previene **ataques de confusión de contexto**. Sin ella, un adversario puede reutilizar hashes de un contexto (ej: nodo Merkle) en otro (ej: challenge FRI), rompiendo la seguridad del protocolo.

**Principio fundamental**: Cada uso del hash debe incluir un identificador único de contexto.

---

## 1. SAFE: Sponge API for Field Elements

**Autores**: JP Aumasson (Taurus), Dmitry Khovratovich (Ethereum Foundation), Bart Mennink (Radboud), Porcu Quine (Lurk Lab)
**Fecha**: Abril 2023
**Referencia**: https://github.com/filecoin-project/neptune/tree/master/src/sponge

### 1.1 Problema que Resuelve

SAFE identifica y resuelve **4 patrones de mal uso** en implementaciones ZK de sponges:

| # | Problema | Impacto |
|---|----------|---------|
| 1 | Sin padding cuando input llena el rate | Colisiones entre mensajes de diferente longitud |
| 2 | Colisiones cross-protocol | Dos protocolos producen mismo output para mismo input |
| 3 | Permutaciones superfluas | Overhead de performance innecesario |
| 4 | Construcciones custom anidadas | Rompe pruebas de seguridad |

### 1.2 Mecanismo de Domain Separation

SAFE computa un **tag** único basado en:
1. **IO Pattern**: Secuencia de operaciones ABSORB/SQUEEZE
2. **Domain Separator**: String único por aplicación

```
Tag = H(serialize(aggregate(encode(IO_pattern))) || domain_separator)
```

**Paso 1: Encode**
- MSB = 1 para ABSORB, MSB = 0 para SQUEEZE
- Lower 31 bits = número de elementos

```
[ABSORB(3), ABSORB(3), SQUEEZE(1)] → [0x80000003, 0x80000003, 0x00000001]
```

**Paso 2: Aggregate**
- Combinar calls consecutivos del mismo tipo

```
[0x80000003, 0x80000003] → [0x80000006]
```

**Paso 3: Serialize + Domain**
- Convertir a bytes + append domain separator

**Paso 4: Hash**
- Aplicar SHA3-256 para obtener tag de 256 bits

### 1.3 Inyección del Tag

El tag se **añade a la parte de capacity** (inner state), NO al rate:
- Si field elements ≥ 248 bits: tag como un field element
- Sino: tag como múltiples field elements (máximo c/2)

### 1.4 API Core

| Operación | Firma | Propósito |
|-----------|-------|-----------|
| `START` | `(IOPattern, DomainSeparator)` | Inicializar, computar e inyectar tag |
| `ABSORB` | `(Length, Data[])` | Ingerir L field elements |
| `SQUEEZE` | `(Length) → F^L` | Extraer L field elements |
| `FINISH` | `() → Result` | Terminar, verificar compliance |

### 1.5 Algoritmos de Ejemplo

**Merkle Hash 2-to-1**:
```python
def merkle_hash(left, right, domain="MerkleTree"):
    io_pattern = [ABSORB(2), SQUEEZE(1)]
    START(io_pattern, domain)
    ABSORB(2, [left, right])
    result = SQUEEZE(1)
    FINISH()
    return result
```

**Fiat-Shamir Transcript**:
```python
def sigma_transcript(Z, pi1, pi2, pi3, domain="FRI"):
    io_pattern = [
        ABSORB(len(Z)),   # Common input
        ABSORB(len(pi1)), # Proof element 1
        SQUEEZE(1),       # Challenge c1
        ABSORB(len(pi2)), # Proof element 2
        SQUEEZE(1),       # Challenge c2
    ]
    START(io_pattern, domain)
    ABSORB(len(Z), Z)
    ABSORB(len(pi1), pi1)
    c1 = SQUEEZE(1)
    ABSORB(len(pi2), pi2)
    c2 = SQUEEZE(1)
    FINISH()
    return (c1, c2)
```

### 1.6 Teorema de Seguridad

> **Teorema 1**: Si un protocolo P es seguro en el modelo de random oracle con oráculos R1...Rk,
> entonces la implementación con cada Ri instanciado vía SAFE con domain separators distintos
> es segura contra adversarios que hacen hasta 2^λ queries.

**Requisitos**:
- Field size ≥ 2^(2λ) para λ-bit security
- Domain separators pairwise distintos

---

## 2. Weak Fiat-Shamir Attacks

**Autores**: Dao, Miller, Wright, Grubbs
**Hallazgo clave**: 36 implementaciones vulnerables en producción

### 2.1 Weak vs Strong Fiat-Shamir

| Tipo | Qué hashea | Seguridad |
|------|------------|-----------|
| **Weak** | Solo mensajes del prover | Vulnerable a ataques adaptativos |
| **Strong** | Parámetros públicos + inputs públicos + mensajes | Seguro |

### 2.2 Template de Ataque

1. Identificar valores públicos NO incluidos en el hash
2. Generar valores de prueba aleatorios
3. Computar challenges desde esos valores
4. Resolver para inputs públicos que satisfagan verificación

### 2.3 Vulnerabilidades Documentadas

| Sistema | Impacto |
|---------|---------|
| **Bulletproofs** | Forjar range proofs (86ms para 32-bit) |
| **Plonk** | Forjar proofs manipulando inputs públicos |
| **Dusk Network testnet** | Crear dinero ilimitado |
| **Wesolowski VDF** | Falsificar parámetro de delay |

### 2.4 Checklist de Auditoría

- [ ] Parámetros públicos (field, domain size, generators) hasheados primero
- [ ] Inputs públicos del circuito incluidos en transcript
- [ ] Merkle roots absorbidos antes de query challenges
- [ ] FRI-specific: evaluation domain, rate, folding factor bound
- [ ] Sin reinicialización de transcript en subprotocolos
- [ ] Cada challenge depende de TODOS los mensajes previos

### 2.5 Causa Raíz

> "Creemos que la alta fracción de implementaciones vulnerables es resultado de un typo
> (ya corregido) en el paper original de Bulletproofs, que especificaba weak F-S."

**Lección**: Las especificaciones deben ser explícitas sobre qué incluir en el hash.

---

## 3. ethSTARK Documentation

**Fuente**: StarkWare Industries Ltd.
**Versión**: 1.2 (Julio 2023)

### 3.1 Domain Separation Estructural

ethSTARK usa **separación por estructura algebraica**, no tags string:

| Elemento | Dominio/Campo |
|----------|---------------|
| Trace columns | F_p |
| Constraint randomness | K = F_p(φ) (extensión) |
| DEEP query point z | K* \ (H₀ ∪ D̄) |
| FRI challenges | K |

### 3.2 Dominios Disjuntos

- **Trace Domain (H₀)**: Subgrupo multiplicativo tamaño N = 2^h
- **Evaluation Domain (D)**: Coset con offset = 3
- **Garantía**: H₀ ∩ D = ∅ por construcción

### 3.3 Estructura de Transcript

```
Round 1: Prover → Execution trace oracle
Round 2: Verifier → Constraint randomness r ∈ K^(2s)
Round 3: Prover → Constraint trace oracle
Round 4: Verifier → DEEP query q ∈ K* \ (H₀ ∪ D̄)
Round 5: Prover → DEEP answer
Round 6: Verifier → FRI combination randomness r^F
Round 7: FRI protocol (múltiples sub-rounds)
```

### 3.4 Seed Inicial

```
seed = Hash("Rescue hash chain" || chain_length || output[0..3])
```

### 3.5 FRI Layer Domains

```
Layer 0: D        (size 2^k')
Layer 1: D²       via x → x² map
Layer 2: D⁴       via x → x² map
...
Layer r: constant polynomial
```

**Requisito**: Cada domain L debe ser cerrado bajo negación (x ∈ L ⇒ -x ∈ L).

---

## 4. Cryptographic Sponge Functions

**Autores**: Bertoni, Daemen, Peeters, Van Assche (equipo Keccak)

### 4.1 Construcción Sponge

```
State = Rate (r bits) || Capacity (c bits)

Absorb: XOR input into rate, then permute
Squeeze: Output from rate, then permute
```

### 4.2 Seguridad

- **Collision resistance**: c/2 bits
- **Preimage resistance**: c/2 bits
- **Indifferentiability**: Hasta 2^(c/2) queries

### 4.3 Padding

Regla 10*1: Append bit 1, luego ceros, luego bit 1 para completar bloque.

**Propósito**: Evitar ataques de extensión de longitud.

---

## 5. Concrete Fiat-Shamir Security

**Autores**: Kiltz, Lyubashevsky, Schaffner (2018)
**Modelo**: QROM (Quantum Random Oracle Model)

### 5.1 Bound de Seguridad

```
Adv^{UF-CMA}(A) ≤ Adv^{LOSS}(B) + Q_H² · ε_ls + Q_S · ε_zk + 2^{-α}
```

**Pérdida cuadrática**: En QROM, la pérdida es Q_H² (no Q_H como en ROM clásico).

### 5.2 Parámetros para 128-bit Security

| Parámetro | Valor Mínimo |
|-----------|--------------|
| Hash output | 256 bits |
| Challenge space | 2^256 |
| Min-entropy de commitments | 256 bits |
| ε_ls (lossy soundness) | < 2^{-256} |

### 5.3 Recomendación de Domain Separation

```c
H_commit(x)   = H(0x01 || x)    // Para commitments
H_challenge(x) = H(0x02 || x)   // Para challenges
H_response(x)  = H(0x03 || x)   // Para responses
```

---

## 6. Concrete Non-Interactive FRI

**Autores**: Block & Tiwari

### 6.1 Hallazgo Crítico

> "La mayoría de sistemas FRI desplegados tienen 21-63 bits MENOS de seguridad
> probable que su objetivo, confiando en conjeturas."

### 6.2 Bounds de Seguridad

**Seguridad Probable**:
```
ε_rbr = max{(m+1/2)^7 · |L₀|² / (3·ρ^{3/2}·|F|), (1-δ)^l}
```

**Seguridad Conjeturada**:
```
ε_rbr = max{1/|F|, (1-δ)^l}
```

### 6.3 Parámetros Recomendados (100-bit security)

| Parámetro | Valor |
|-----------|-------|
| Field size | ≥ 192 bits (probable) |
| Hash output κ | 256 bits |
| Rate ρ | 1/4 a 1/8 |

### 6.4 Grinding

Añade `z` bits de seguridad: prover debe encontrar nonce con `z` leading zeros.

---

## 7. To Pad or Not to Pad

**Autores**: Lefevre, Marhuenda Beltran, Mennink

### 7.1 Problema

Para campos grandes (p ~ 2^256), el padding tradicional desperdicia hasta 50% de permutaciones.

### 7.2 Solución: NCP (Non-Cryptographic Permutation)

En lugar de padding con bits, usar funciones simples para separar contextos:

```
π^p(x) = x           // Partial block (identity)
π^f(x) = x + C       // Full block (add constant)
```

### 7.3 Constraints de Seguridad

**Constraint 1**: Para cualquier x:
```
π^p(x) ≠ π^f(x)  AND  x ≠ π^f(x)
```

**Constraint 2**: Para IVs distintos IV₁, IV₂:
```
{IV₁, π^f(IV₁), π^p(IV₁)} ∩ {IV₂, π^f(IV₂), π^p(IV₂)} = ∅
```

### 7.4 Implementación Simple

```
C_full ≠ 0 (constante no-cero)
C_squeeze ≠ C_full

π^f(x) = x + C_full
π^p(x) = x
π^s(x) = x + C_squeeze
```

---

## 8. Poseidon Paper

**Autores**: Grassi et al. (USENIX 2021)

### 8.1 Domain Separation Explícito (Section 4.2)

| Uso | Valor en Capacity |
|-----|-------------------|
| Merkle tree (arity ≤ 32) | `2^arity - 1` |
| Merkle tree sparse | Bitmask de hojas presentes |
| Hash variable-length | `2^64 + (o-1)` donde o = output length |
| Hash fixed-length | `length * 2^64 + (o-1)` |
| Encryption | `2^32` |
| Custom protocol | `identifier * 2^32` |

### 8.2 Ubicación del Separator

> El domain separator se coloca en el **capacity element** (inner state), NO en el rate.

### 8.3 Margen de Seguridad

Después de calcular rounds mínimos contra ataques conocidos:
- +2 full rounds (R_F)
- +7.5% partial rounds (R_P)

---

## 9. Generalized Indifferentiable Sponge

**Autores**: Ashur & Bhati

### 9.1 Indifferentiability

Mide cuán cercano es un hash H (con permutación interna) a un random oracle.

**Garantía**: Si H es indifferentiable de RO, cualquier criptosistema basado en RO
es al menos igual de seguro cuando se instancia con H.

### 9.2 Bound de Seguridad

Para Sponge2 con r₀ = c/2:
```
Adv ≤ 3·Q_P / p^{c/2}
```

**Para Poseidon2 con p ~ 2^64, c = 4**: ~126 bits de seguridad.

### 9.3 Condiciones para Composición Segura

1. **Padding inyectivo**: padding(M₁) ≠ padding(M₂) si M₁ ≠ M₂
2. **Sin colisiones de capacity**: Outputs no deben tener capacity igual a inputs previos
3. **Domain separator en capacity**: NO en rate
4. **Capacity suficiente**: c ≥ 2M para M-bit security

---

## Síntesis: Aplicación a AMO-Lean Step 5.2

### Gaps Identificados en Nuestro Código

| Archivo | Issue | Fuente |
|---------|-------|--------|
| `Integration.lean` | Domain tags como primos pequeños (2,3,5...) | Debería usar scheme de Poseidon paper |
| `Transcript.lean` | Squeeze usa XOR, no Poseidon2 | Weak F-S risk |
| `Integration.lean` vs `Transcript.lean` | Tags no unificados | Inconsistencia |
| General | Sin validación de IO pattern | SAFE recomienda verificar |

### Acciones para Step 5.2

1. **Unificar DomainTags**: Crear enum compartido entre Integration.lean y Transcript.lean
2. **Adoptar scheme Poseidon**: Usar `2^arity - 1` para Merkle, etc.
3. **Verificar transcript binding**: Auditar Protocol.lean para weak F-S
4. **Documentar gaps**: Crear ADR con decisiones tomadas

### Checklist de Auditoría Final

- [ ] Cada uso de hash tiene domain tag único
- [ ] Tags en capacity, no en rate
- [ ] Parámetros públicos absorbidos antes de challenges
- [ ] Merkle roots absorbidos antes de query phase
- [ ] Sin reinicialización de transcript
- [ ] IO pattern documentado para cada función hash

---

## Referencias

1. SAFE Sponge API - https://eprint.iacr.org/2023/522
2. Weak Fiat-Shamir - https://eprint.iacr.org/2019/426
3. ethSTARK Documentation v1.2 - StarkWare
4. Cryptographic Sponge Functions - Keccak Team
5. Concrete Fiat-Shamir Security - https://eprint.iacr.org/2016/771
6. Concrete Non-Interactive FRI - Block & Tiwari
7. To Pad or Not to Pad - https://eprint.iacr.org/2023/1510
8. Poseidon - https://eprint.iacr.org/2019/458
9. Generalized Indifferentiable Sponge - Ashur & Bhati

---

*Última actualización: 2026-01-27*
