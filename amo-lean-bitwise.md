# AMO-Lean: Descubrimiento de Identidades Algebraicas Bitwise — Análisis Crítico

## Contexto

Análisis de la propuesta de extender el motor E-graph de amo-lean para descubrir identidades algebraicas específicas de cuerpos finitos (Mersenne31, BabyBear, Goldilocks) que exploten operaciones a nivel de bit (shifts, AND, XOR) para reemplazar multiplicaciones modulares costosas.

---

## Estado Actual de amo-lean (v3.0.0)

### Motor E-graph
- `CircuitNodeOp`: 7 constructores puramente algebraicos (`addGate`, `mulGate`, `negGate`, `smulGate`, `constGate`, `witness`, `pubInput`)
- Zero operaciones bitwise
- Semántica anclada en `ConsistentValuation` con 121 teoremas y zero axiomas
- Pipeline `saturateF → extractF` con soundness probado end-to-end
- Framework genérico `NodeOps` + `NodeSemantics` (VerifiedExtraction) — extensible a nuevos tipos de operación

### Campos Finitos Verificados
- Mersenne31 (2^31 - 1): UInt32, 889 LOC, Field instance, toZMod homomorfismo
- BabyBear (15 × 2^27 + 1): UInt32, 901 LOC, Field instance, toZMod homomorfismo
- Goldilocks (2^64 - 2^32 + 1): UInt64, 1522 LOC, Field instance, Lucas primality
- Montgomery reduction genérica verificada (337 LOC)
- Plonky3Field typeclass unificado (180 LOC)
- Translation Validation: roundtrip BabyBear Montgomery probado

---

## Análisis de la Propuesta (Gemini QA)

### Donde Gemini acierta

**1. La idea nuclear es matemáticamente sólida.** Los "trucos" de BabyBear/Mersenne31 son consecuencias algebraicas de la estructura de `p` en base 2. La identidad `2^31 ≡ 1 (mod 2^31 - 1)` para Mersenne31 *es* una regla de reescritura. Que el E-graph la descubra componiendo reglas genéricas (asociatividad, distributividad) con reglas de bits (shift = multiplicar por potencia de 2) es teóricamente factible.

**2. La verificación formal del resultado es el verdadero diferenciador.** Si el E-graph "escupe" una secuencia de shifts y ANDs, probar que eso es idéntico a `a * b % p` en `ZMod p` es donde amo-lean tiene ventaja única. Nadie más tiene la infraestructura para hacer esto.

**3. La saturación por fases es la estrategia correcta** para controlar la explosión. Fase 1 algebraica, Fase 2 de máquina. Esto ya lo hacen herramientas como Herbie (University of Washington) para floating point.

### Donde Gemini se equivoca o simplifica peligrosamente

**1. El puente BitVec ↔ ZMod es órdenes de magnitud más difícil de lo que sugiere.**

El teorema que Gemini escribe casualmente:
```lean
theorem bitwise_reduction_correct (x y : BitVec 64) :
  to_ZMod p (evalMixedExpr (.mul_mod x y)) =
  (to_ZMod p x) * (to_ZMod p y)
```

Esto parece un teorema. En realidad es un **programa de investigación**. Para probarlo necesitas:

- Un modelo formal de `BitVec n` con semántica de overflow definida (Mathlib lo tiene parcialmente, pero `BitVec.shiftRight` y `BitVec.and` no tienen la cobertura de lemas que necesitarías).
- Lemas de conexión `BitVec n → Nat → ZMod p`. El camino `BitVec → toNat → (coe : Nat → ZMod p)` existe, pero los lemas intermedios (e.g., `(x &&& y).toNat = x.toNat &&& y.toNat` para Nat bitwise) no están todos en Mathlib.
- Razonamiento sobre **overflow de 128 bits** para la multiplicación Goldilocks (el producto `x * y` donde x, y < 2^64 cabe en 128 bits, pero Lean no tiene `UInt128` ni `BitVec 128` bien soportado).

Estimación: construir este puente formalmente verificado costaría **2,000-4,000 LOC** de lemas auxiliares solo para la infraestructura, antes de probar un solo teorema de optimización.

**2. "Superar a Montgomery/Barrett escrita a mano" es una afirmación extraordinaria sin evidencia.**

20 años en la industria de hardware dicen esto: Montgomery reduction (1985), Barrett reduction (1986), y Mersenne folding son el resultado de **40 años de refinamiento** por miles de ingenieros. La probabilidad de que un E-graph descubra algo genuinamente superior es baja.

Lo que SÍ puede hacer el E-graph, y esto es valioso:
- **Redescubrir** estas técnicas a partir de principios (validación independiente)
- **Componer** técnicas conocidas de formas no exploradas (e.g., interleaving de reducción con butterfly NTT)
- **Especializar** para un primo nuevo en minutos en vez de semanas

Pero "Zero-Day Optimizations" es marketing, no ingeniería.

**3. El modelo de costos es naive.**

Gemini dice "1 ciclo para shift, 15-40 para división". En hardware real:

| Factor | Impacto en optimización |
|--------|------------------------|
| **Pipelining** | Una multiplicación de 3 ciclos de latencia puede tener throughput de 1/ciclo si es pipelined |
| **Superscalar** | ARM Cortex-A76 ejecuta 2 MUL + 2 ADD por ciclo |
| **Register pressure** | Un "truco" con 8 variables intermedias puede ser peor que una MUL directa si spills a memoria |
| **Carry chains** | En FPGA/ASIC, la propagación de carry domina el timing, no el tipo de operación |
| **Branch prediction** | Un `if` en reducción condicional tiene costo de misprediction |
| **Memoria** | Acceso a lookup table para inversas puede costar 100+ ciclos (cache miss) |

Un E-graph con cost function `mulGate = 1, resto = 0` (que es lo que amo-lean tiene ahora) **no puede capturar esto**. Se necesita un modelo de costos paramétrico por microarquitectura.

**4. La "explosión del E-graph" está subestimada.**

La combinación de reglas algebraicas (asociatividad, conmutatividad, distributividad — ya dan O(n^3) nodos para n operaciones) con reglas bitwise (shift distributes over add, mask-and-shift identities) produce un espacio de estados que es **exponencial en la profundidad del circuito**. Herbie, que hace algo similar para floating point, tiene:
- Límites agresivos de iteraciones (< 100)
- Pruning basado en intervalos (elimina expresiones que no mejoran precisión)
- Todavía se cuelga en expresiones de más de ~15 operaciones

Para una multiplicación modular que involucra 5-8 operaciones bitwise, el E-graph es manejable. Para un pipeline FRI completo de profundidad 20+, **no va a saturar en horas ni en días**.

---

## Evaluación: ¿Vale la pena?

**Sí, pero no por las razones que Gemini da.** El valor no está en "descubrir optimizaciones que humanos no pueden encontrar". Está en:

1. **Verificación automática de implementaciones existentes**: Alguien escribe un truco de bits para BabyBear, lo inyecta como candidato, el E-graph verifica que es equivalente al multiplicador canónico.

2. **Portabilidad verificada entre campos**: Defines `p` nuevo → el framework genera automáticamente la aritmética verificada. Esto SÍ tiene valor industrial real (cada nuevo campo ZK toma meses de implementación y auditoría).

3. **Scheduling verificado de reducción lazy**: En NTT/FRI, puedes acumular varias sumas antes de reducir (si no hay overflow). Probar formalmente hasta dónde puedes retrasar la reducción es un problema real y valioso.

---

## Plan de Acción: Tres Alternativas

### Alternativa A: "El E-graph como verificador" (Menor riesgo, mayor ROI inmediato)

**Concepto**: No intentar que el E-graph *descubra* trucos bitwise. En cambio, usar el E-graph para *verificar* que implementaciones bitwise conocidas son semánticamente equivalentes a la aritmética abstracta.

**Alcance**:
1. Extender `CircuitNodeOp` con `shiftLeft`, `shiftRight`, `bitAnd`, `bitMask`
2. Definir `evalOp` para las nuevas operaciones sobre `Nat` (no BitVec — evitas todo el dolor del puente)
3. Inyectar la implementación Plonky3 (e.g., `monty_reduce` como secuencia de shift/and/add) como expresión en el E-graph
4. Inyectar la especificación (`a * b % p`) como otra expresión
5. Dejar que el E-graph las una mediante reglas (sin necesidad de saturación completa — basta con que encuentre el path)
6. El `extractF_correct` existente te da la prueba

**Estimación**: 2,000-3,000 LOC, 3-5 semanas. Reutiliza 90% de la infraestructura existente.

**Estructura de módulos** (dentro de `AmoLean/`):
- **Capa 1 — Extensión del AST**: Agregar constructores bitwise a `CircuitNodeOp` o crear `MixedNodeOp`
- **Capa 2 — Reglas de reescritura campo-específicas**: `SoundRewriteRule` instances para identidades bitwise
- **Capa 3 — Bridge bitwise ↔ algebraico**: Lemas Nat bitwise ↔ aritmética modular
- **Capa 4 — Verificación**: Extender `extractF_correct` o instanciar `NodeOps` + `NodeSemantics` para el nuevo tipo

El framework genérico de `VerifiedExtraction/` ya soporta esto — `NodeOps` y `NodeSemantics` son typeclasses genéricas no atadas a `CircuitNodeOp`.

**Fuentes necesarias**:
- Montgomery original (1985): "Modular multiplication without trial division"
- Barrett (1986): "Implementing the Rivest Shamir and Adleman public key encryption algorithm"
- Plonky3 source code (ya se usa para TV)

### Alternativa B: "Síntesis de reducción por campo" (Riesgo medio, alto valor de investigación)

**Concepto**: Dado un primo `p`, sintetizar automáticamente la mejor secuencia de reducción usando E-graph + cost model parametrizado.

**Alcance**:
1. Todo lo de Alternativa A
2. Cost model parametrizado: `CostModel` typeclass con latencia/throughput por operación
3. Reglas de reescritura genéricas que codifican la identidad `2^k ≡ c (mod p)` para las potencias de 2 relevantes del primo
4. Saturación acotada (fuel ~50 iteraciones) sobre expresiones de tamaño ≤ 10 nodos
5. Extracción con el cost model del target (ARM, RISC-V, FPGA)
6. Verificación: el resultado es semánticamente equivalente a `a * b % p`

**Estimación**: 5,000-8,000 LOC, 8-12 semanas. Requiere investigación original en el cost model.

**Fuentes necesarias** (además de Alternativa A):
- **Fiat-Crypto** (MIT, 2019): "Simple High-Level Code For Cryptographic Arithmetic — With Proofs, Without Compromises"
- **egg paper** (Willsey et al., POPL 2021): "egg: Fast and extensible equality saturation"
- **ruler** (Nandi et al., OOPSLA 2021): "Rewrite Rule Inference Using Equality Saturation"
- ARM Architecture Reference Manual (para cost model ARM)
- RISC-V ISA specification v2.2 (para cost model RISC-V)
- Agner Fog's instruction tables (x86 latencia/throughput por microarquitectura)

### Alternativa C: "El programa completo" (Alto riesgo, potencial de paper top-tier)

**Concepto**: Lo que Gemini propone, pero con alcance realista y timeline honesto.

**Alcance**:
1. Infraestructura BitVec ↔ ZMod (puente formal completo)
2. MixedExpr AST con semántica dual (algebraica + bitwise)
3. Saturación por fases con phase ordering configurable
4. Cost model multi-target (CPU, FPGA, ASIC)
5. Síntesis verificada end-to-end: `p` → aritmética de máquina → prueba de correctness
6. Benchmarks contra Fiat-Crypto y implementaciones manuales

**Estimación**: 15,000-25,000 LOC, 6-12 meses. Es un paper de PLDI/POPL.

**Fuentes necesarias** (además de A y B):
- **Mathlib BitVec**: Estado actual de `Mathlib.Data.BitVec` y `Std.BitVec`
- **CryptOpt** (Kuepper et al., PLDI 2022): "CryptOpt: Verified Compilation with Random Program Search for Cryptographic Primitives"
- **Jasmin/EasyCrypt**: Framework de verificación de crypto con extraction a assembly
- **Documentación de hardware**:
  - Intel Intrinsics Guide (para SIMD: `_mm256_mul_epu32`, etc.)
  - FPGA documentation (Xilinx UltraScale+ DSP48E2 para multiplicadores en hardware)
  - ASIC synthesis: Synopsis Design Compiler cost models
- **Papers de campos finitos para ZK**:
  - "Goldilocks: The Field of Scalars for the Plonky3 Protocol" (Polygon)
  - "BabyBear and KoalaBear" (Plonky3 documentation)
- **Herbie** (Panchekha et al., PLDI 2015): Control de explosión en E-graphs

---

## Fuentes Críticas por Categoría

### Cuerpos Finitos + Aritmética Modular
| Fuente | Por qué es necesaria |
|--------|---------------------|
| Montgomery (1985) | Fundamento de REDC, ya parcialmente en amo-lean |
| Barrett (1986) | Alternativa a Montgomery para campos donde es más eficiente |
| **Fiat-Crypto (MIT)** | **Competidor directo** — benchmark de comparación |
| Handbook of Applied Cryptography, Ch. 14 | Catálogo completo de técnicas de aritmética modular |
| Crandall (1994) | Reducción específica para primos Mersenne y pseudo-Mersenne |

### Hardware y Modelos de Costo
| Fuente | Por qué es necesaria |
|--------|---------------------|
| Agner Fog instruction tables | Latencia/throughput real por microarquitectura x86 |
| ARM Cortex-A series TRM | Cost model para mobile/embedded (donde ZK se ejecuta) |
| RISC-V ISA spec + rocket-chip | Target emergente para ZK hardware |
| Xilinx DSP48E2 user guide | Si se contempla FPGA, los multiplicadores DSP son el cuello de botella |
| Patterson & Hennessy, "Computer Organization and Design" | Fundamentos de pipeline, hazards, cost modeling |

### E-Graphs y Síntesis
| Fuente | Por qué es necesaria |
|--------|---------------------|
| egg (Willsey et al., POPL 2021) | E-graph canónico, límites de escalabilidad |
| Herbie (Panchekha et al., PLDI 2015) | Caso de estudio: E-graph para floating point, problemas de explosión |
| ruler (Nandi et al., OOPSLA 2021) | Inferencia automática de reglas |
| CryptOpt (Kuepper et al., PLDI 2022) | Mismo problema con random search en vez de E-graphs |
| STOKE (Schkufza et al., ASPLOS 2013) | Superoptimización estocástica — baseline de comparación |

### Verificación Formal de Crypto
| Fuente | Por qué es necesaria |
|--------|---------------------|
| Fiat-Crypto (Erbsen et al., S&P 2019) | Síntesis verificada de aritmética modular (Coq). Competidor directo |
| Jasmin (Almeida et al., CCS 2017) | Verificación de crypto a nivel assembly |
| Vale (Bond et al., USENIX 2017) | Verificación de AES/SHA en assembly |
| hacspec | Especificación de crypto en Rust + verificación |

---

## Recomendación

**Empezar por Alternativa A, evolucionar hacia B.** Razones:

1. **A da resultados publicables en ~1 mes**: "Verified bitwise equivalence of Plonky3 field arithmetic via equality saturation" es un resultado sólido.

2. **A valida la viabilidad antes de invertir en B o C**: Si extender `CircuitNodeOp` con bitwise ops rompe el rendimiento del E-graph o hace las pruebas intratables, se descubre con ~3,000 LOC de inversión, no con 25,000.

3. **El benchmark crítico es Fiat-Crypto**: Antes de planificar C, hay que entender exactamente qué hace Fiat-Crypto y dónde amo-lean puede ser complementario o superior.

4. **El cost model es un proyecto separado**: Hacer B bien requiere un CostModel serio. El cost model debería ser un deliverable independiente, no embedded en el E-graph. Así se puede iterar sobre él sin re-probar soundness.
