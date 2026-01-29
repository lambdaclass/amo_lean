# Fase 5: Bibliografía Completa

**Fecha de creación**: 2026-01-29
**Propósito**: Documentar todas las fuentes estudiadas para Phase 5 NTT

---

## 1. Papers Fundamentales (PDFs en `docs/references/ntt/`)

### 1.1 Verificación Formal de NTT

| # | Paper | Autores | Año | Archivo |
|---|-------|---------|-----|---------|
| P1 | **Formally Verified NTT** | Trieu et al. (ANSSI) | 2025 | `formally verified ntt.pdf` |
| P2 | **Verification of an Optimized NTT** | Navas, Dutertre | 2023 | `verification of an optimized ntt.pdf` |

**P1 - Trieu et al. (CRÍTICO)**
- **Aporte principal**: Especificación CRT-based superior a evaluation-based
- **Técnica**: Refinamiento por 4 capas (spec → recursivo → bounds → iterativo)
- **Esfuerzo**: 7 meses de trabajo en Coq
- **Herramientas**: MathComp, Bedrock2, Fiat-Crypto
- **Aplicación en AMO-Lean**: Adoptamos su modelo de capas (DD-011)

**P2 - Navas & Dutertre**
- **Aporte principal**: Ausencia de overflow via interpretación abstracta
- **Técnica**: Abstract interpretation para tracking de bounds
- **Aplicación en AMO-Lean**: Inspira nuestro enfoque de tipos refinados para bounds

### 1.2 Optimizaciones Algorítmicas

| # | Paper | Autores | Año | Archivo |
|---|-------|---------|-----|---------|
| P3 | **Faster Arithmetic for NTT** | Harvey | 2014 | `faster arithmetic ntt.pdf` |
| P4 | **NTT Optimization Using Harvey** | (varios) | 2020 | `ntt optimization using harvey.pdf` |
| P5 | **Note on Implementation of NTT** | -- | -- | `note on implementation of ntt.pdf` |

**P3 - Harvey's Algorithm (MUY IMPORTANTE)**
- **Aporte principal**: Representación redundante [0, 2p) para butterflies
- **Beneficio**: Elimina condicionales en lazy reduction
- **Fórmula**: `if x >= p then x - p` → `x - p + (x < p ? p : 0)`
- **Aplicación en AMO-Lean**: Base para LazyGoldilocks (DD-014)

**P4 - Harvey Optimization**
- **Aporte principal**: Aplicación práctica de Harvey a implementaciones reales
- **Benchmark**: ~20% speedup vs Montgomery reduction
- **Aplicación en AMO-Lean**: Guía para CodeGen optimizado

### 1.3 Fundamentos Matemáticos

| # | Paper | Autores | Año | Archivo |
|---|-------|---------|-----|---------|
| P6 | **Introduction to NTT** | -- | -- | `intro to ntt.pdf` |
| P7 | **Implementing NTT** | -- | -- | `implementing ntt.pdf` |

**P6 - Intro to NTT**
- **Contenido**: Definición matemática, relación con FFT, propiedades algebraicas
- **Aplicación en AMO-Lean**: Base teórica para Spec.lean

**P7 - Implementing NTT**
- **Contenido**: Cooley-Tukey vs Gentleman-Sande, bit-reversal, twiddle factors
- **Aplicación en AMO-Lean**: Guía para CooleyTukey.lean

### 1.4 Contexto Criptográfico

| # | Paper | Autores | Año | Archivo |
|---|-------|---------|-----|---------|
| P8 | **NTT for CRYSTALS** | -- | -- | `ntt for crystal.pdf` |
| P9 | **NTT Meets SIS** | -- | -- | `ntt meets sis.pdf` |

**P8 - NTT for CRYSTALS**
- **Contenido**: NTT en Kyber/Dilithium, parámetros reales
- **Aplicación en AMO-Lean**: Validación de que nuestro enfoque es compatible con criptografía real

**P9 - NTT Meets SIS**
- **Contenido**: Aplicaciones de NTT en lattice-based crypto
- **Aplicación en AMO-Lean**: Contexto para futuras extensiones

### 1.5 Hardware y Paralelismo

| # | Paper | Autores | Año | Archivo |
|---|-------|---------|-----|---------|
| P10 | **Pipelined NTT** | -- | -- | `pipelined ntt.pdf` |
| P11 | **NTT Accel via Design Time Constants** | -- | -- | `ntt accel via design time constants.pdf` |

**P10 - Pipelined NTT**
- **Contenido**: Arquitectura de pipeline para NTT en hardware
- **Aplicación en AMO-Lean**: Insights para paralelismo AVX2 futuro

**P11 - NTT Acceleration**
- **Contenido**: Precomputación de twiddle factors
- **Aplicación en AMO-Lean**: Optimización para CodeGen

---

## 2. Repositorios de Código

### 2.1 risc0-lean4

| Atributo | Valor |
|----------|-------|
| **URL** | https://github.com/risc0/risc0-lean4 |
| **Lenguaje** | Lean 4 |
| **Relevancia** | CRÍTICA |

**Contenido relevante**:
- Type classes para campos (`Field.lean`)
- NTT ejecutable sobre listas (sin pruebas formales)
- Estructura de proyecto Lean 4 para ZK

**Aprendizajes para AMO-Lean**:
- Usar hierarchy ligera paralela a Mathlib (DD-013)
- `IsPrimitiveRoot` solo necesita `CommMonoid`
- Pattern de definir `NTTField` sin depender de `Field` completo de Mathlib

### 2.2 GPU-NTT

| Atributo | Valor |
|----------|-------|
| **URL** | https://github.com/Alisah-Ozcan/GPU-NTT |
| **Lenguaje** | CUDA |
| **Relevancia** | MEDIA |

**Contenido relevante**:
- Barrett reduction implementación
- Batch processing de múltiples NTTs
- Memory coalescing patterns

**Aprendizajes para AMO-Lean**:
- Técnicas de optimización traducibles a AVX2
- Estructura de datos para NTT in-place

---

## 3. Documentación de Lean 4

### 3.1 Functional Programming in Lean

| Atributo | Valor |
|----------|-------|
| **URL** | https://lean-lang.org/functional_programming_in_lean/ |
| **Capítulos relevantes** | Monads, Do-Notation, Arrays |

**Aprendizajes**:
- `Array` vs `List` en Lean 4
- ST Monad para estado mutable local
- Pattern matching en arrays

### 3.2 Theorem Proving in Lean 4

| Atributo | Valor |
|----------|-------|
| **URL** | https://lean-lang.org/theorem_proving_in_lean4/ |
| **Capítulos relevantes** | Induction, Tactics, Structures |

**Aprendizajes**:
- Inducción estructural y generalizada
- Uso de `omega` para aritmética
- Definición de estructuras con invariantes

### 3.3 Mathlib4 Documentation

| Atributo | Valor |
|----------|-------|
| **URL** | https://leanprover-community.github.io/mathlib4_docs/ |
| **Módulos relevantes** | `IsPrimitiveRoot`, `ZMod`, `CommMonoid` |

**Aprendizajes**:
- `IsPrimitiveRoot` es ligero (solo necesita `CommMonoid`)
- Evitar `Field` de Mathlib (requiere `ratCast`)
- Usar teoremas existentes sobre raíces de unidad

### 3.4 Lean 4 Reference Manual

| Atributo | Valor |
|----------|-------|
| **URL** | https://lean-lang.org/doc/reference/latest/ |
| **Secciones relevantes** | Std.Do, mvcgen |

**Aprendizajes**:
- `mvcgen` para loop invariants (Lean 4.22+)
- `Std.Do` para do-notation mejorada
- Decisión: evitar mvcgen por ser muy nuevo (DD-012)

---

## 4. Blogs y Tutoriales

### 4.1 Higashi's NTT Series

| Atributo | Valor |
|----------|-------|
| **URL** | https://higashi.blog/2023/12/15/ntt-03/ |
| **Idioma** | Japonés (con traducción) |

**Contenido**:
- Serie de 3 partes sobre NTT
- Explicación del "Kyber Trick"
- Visualizaciones de butterfly operations

### 4.2 Markus Himmel's Blog

| Atributo | Valor |
|----------|-------|
| **URL** | https://markushimmel.de/ |
| **Artículo relevante** | "First verified imperative program with mvcgen" |

**Aprendizajes**:
- Estado actual de verificación imperativa en Lean 4
- Limitaciones de mvcgen
- Refuerza nuestra decisión de evitar código imperativo (DD-012)

---

## 5. Decisiones de Diseño Derivadas

| ID | Decisión | Fuente Principal |
|----|----------|------------------|
| DD-011 | Especificación CRT-based | P1 (Trieu) |
| DD-012 | No escribir versión iterativa | Manual Lean 4 + Himmel blog |
| DD-013 | NTTField lightweight + IsPrimitiveRoot | risc0-lean4 + Mathlib docs |
| DD-014 | Lazy reduction con tipos refinados | P3 (Harvey) + P2 (Navas) |

---

## 6. Citas Clave

### De Trieu et al. (P1):
> "The key insight is that NTT can be specified using the Chinese Remainder Theorem,
> which naturally handles both complete and incomplete NTT, and makes bit-reversal
> emerge from the algebraic structure."

### De Harvey (P3):
> "By keeping values in the range [0, 2p) instead of [0, p), we can eliminate
> conditional branches in the butterfly operation, trading one comparison for
> predictable arithmetic."

### De Navas & Dutertre (P2):
> "Abstract interpretation provides a sound over-approximation of value ranges,
> allowing us to prove absence of overflow without reasoning about specific inputs."

---

## 7. Lecturas Pendientes (Para Fases Futuras)

| Recurso | Tema | Prioridad |
|---------|------|-----------|
| Fiat-Crypto paper | Síntesis de código verificado | Media |
| Bedrock2 documentation | Separation logic para bajo nivel | Baja |
| VST (Verified Software Toolchain) | Alternativa a Bedrock2 | Baja |

---

*Documento creado: 2026-01-29*
*Última actualización: 2026-01-29*
