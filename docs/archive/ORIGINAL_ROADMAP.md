# AMO-Lean: Automatic Mathematical Optimizer

## Visión General

AMO-Lean es un optimizador matemático automático verificado, diseñado para transformar código Rust (vía Hacspec) en versiones optimizadas con garantías formales de corrección.

## Arquitectura Estratificada

Basándonos en el análisis de las referencias (egg, E-graphs as Circuits, Fiat-Crypto Rewriter), adoptamos una arquitectura de dos niveles:

```
┌─────────────────────────────────────────────────────────────────┐
│                    NIVEL SEMÁNTICO (Lean)                       │
│  • Lean.Expr para representación canónica                       │
│  • MetaM para verificación de tipos e instancias                │
│  • Mathlib como fuente de verdad para reglas                    │
│  • Pruebas de corrección verificadas por el kernel              │
└─────────────────────────────────────────────────────────────────┘
                              ↕
                    [Proyección / Lifting]
                              ↕
┌─────────────────────────────────────────────────────────────────┐
│                   NIVEL SINTÁCTICO (OptExpr)                    │
│  • AST simplificado (similar a HacspecExpr)                     │
│  • E-graph con equality saturation                              │
│  • E-class analyses para tracking de información                │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│                   GENERACIÓN DE CÓDIGO                          │
│  • Lowering a three-address code                                │
│  • Pretty printing a C/Rust                                     │
└─────────────────────────────────────────────────────────────────┘
```

## Decisiones de Diseño Clave

### 1. ¿Por qué no usar Lean.Expr directamente en el E-graph?

**Problema**: `Lean.Expr` tiene binding (λ, ∀), metavariables, universos, etc. El e-matching en egg asume términos de primer orden con aridad fija.

**Solución**: Usar un AST simplificado (`OptExpr`) para el E-graph, con verificación final en `Lean.Expr`.

### 2. PHOAS vs De Bruijn

Del paper de Gross et al.:
> "de Bruijn indices suffer from linear-time lookups and tedious bookkeeping"

**Decisión**: Para el modelo de juguete usamos índices simples. Para el sistema completo, evaluaremos PHOAS en Lean 4.

### 3. Preservación de Sharing (Let-Lifting)

Del paper de Gross et al.:
> "Without sharing, P-256 compilation ran out of memory on 64GB RAM"

**Decisión**: Implementar `UnderLets` o equivalente para preservar lets durante reescritura.

### 4. Integración con Mathlib

Los teoremas de Mathlib tienen la forma:
```lean
theorem mul_comm {M : Type*} [CommMagma M] (a b : M) : a * b = b * a
```

**Desafío**: La aplicación requiere síntesis de instancias de tipo clase.

**Solución**: E-class analysis que consulta `MetaM` en puntos estratégicos, no en cada operación.

---

## Roadmap Detallado

### Fase 1: Modelo de Juguete ✓ (COMPLETADA)

**Objetivo**: Validar la arquitectura básica.

**Completado**:
- [x] `Expr α` inductivo para expresiones aritméticas
- [x] Reglas de reescritura (identidades, distributividad)
- [x] Motor de reescritura bottom-up
- [x] Generación de código C básica
- [x] Esqueleto de pruebas de corrección

---

### Fase 1.5: Verificación Completa ✓ (COMPLETADA - Enero 2026)

**Objetivo**: Cerrar todos los `sorry` y tener pruebas completas.

**Completado**:
- [x] Redefinir `rewriteBottomUp` sin `partial` (usando recursión estructural)
- [x] Redefinir `rewriteToFixpoint` sin `partial` (usando pattern matching sobre Nat)
- [x] Redefinir `lowerExpr` sin `partial` en CodeGen
- [x] Probar `rewriteBottomUp_sound` por inducción sobre `Expr`
- [x] Probar `rewriteToFixpoint_sound` por inducción sobre `fuel`
- [x] Probar `simplify_sound` usando los lemas anteriores
- [x] Lema auxiliar `algebraicRules_sound` para las 6 reglas

**Resultado**: 0 `sorry` en el proyecto. Motor de reescritura completamente verificado.

---

### Fase 1.75: Optimizaciones Pre-E-graph ✓ (COMPLETADA - Enero 2026)

**Objetivo**: Preparar el terreno para E-graphs con optimizaciones de bajo costo.

**Completado**:
- [x] Benchmark baseline (ver `docs/BENCHMARK_FASE1.md`)
- [x] Cost Model: `CostModel` y `exprCost` en Basic.lean
- [x] Constant Folding: `rule_const_fold_add`, `rule_const_fold_mul`
- [x] Asociatividad Dirigida: Evaluada pero descartada (causa 70x slowdown en greedy)
- [x] `simplifyWithConstFold` - función recomendada sin asociatividad
- [x] `simplifyExtended` - función con asociatividad (con advertencia)

**Hallazgos clave**:
- Motor escala O(n): 253k nodos en 0.5s
- Asociatividad no es viable en reescritura greedy
- Esto validó la necesidad de E-graphs para explorar múltiples formas

---

### Fase 2: E-graph y Equality Saturation ✓ (COMPLETADA - Enero 2026)

**Objetivo**: Reemplazar reescritura greedy con equality saturation.

**Archivos creados**:
- `AmoLean/EGraph/Basic.lean` (~530 líneas) - Estructuras y algoritmos core
- `AmoLean/EGraph/EMatch.lean` (~275 líneas) - E-matching y reglas
- `AmoLean/EGraph/Saturate.lean` (~190 líneas) - Saturación y optimización

**Estructuras de datos implementadas**:
- [x] `EClassId`: Índice en array (Nat)
- [x] `ENodeOp`: Operaciones con IDs de hijos (no recursivo)
- [x] `ENode`: Wrapper con helpers (`mkConst`, `mkAdd`, `children`, etc.)
- [x] `EClass`: Clase de equivalencia con nodos y metadata de costo
- [x] `UnionFind`: Path compression con `Array EClassId`
- [x] `EGraph`: Estructura principal (union-find + hashcons + classes)

**Algoritmos implementados**:
- [x] `add(EGraph, ENode) → (EClassId, EGraph)` - Añadir con deduplicación
- [x] `merge(EGraph, EClassId, EClassId) → EGraph` - Unir clases
- [x] `find(EGraph, EClassId) → EClassId` - Encontrar canónico
- [x] `rebuild(EGraph) → EGraph` - Re-canonicalización completa
- [x] `canonicalize` - Normalizar hijos de un nodo

**E-matching implementado**:
- [x] `Pattern` - Patrones con variables (`?a`, `?b`, etc.)
- [x] `Substitution` - Mapeo de variables a e-classes
- [x] `ematch` - Búsqueda de instancias en una e-class
- [x] `searchPattern` - Búsqueda en todo el grafo
- [x] `instantiate` - Crear nodos desde patrón + sustitución

**Reglas de reescritura**:
- [x] `basicRules`: `a+0→a`, `0+a→a`, `a*1→a`, `1*a→a`, `a*0→0`, `0*a→0`
- [x] `extendedRules`: + distributividad (`a*(b+c)→a*b+a*c`) y factorización

**Saturación implementada**:
- [x] `SaturationConfig` - Límites configurables (iteraciones, nodos, clases)
- [x] `saturateStep` - Una iteración (aplicar reglas + rebuild)
- [x] `saturate` - Hasta punto fijo o límite
- [x] `saturateAndExtract` - Saturar + calcular costos + extraer

**Extracción implementada**:
- [x] `EGraphCostModel` - Modelo de costo para E-graph
- [x] `computeCosts` - Cálculo bottom-up iterativo
- [x] `extract` - Extraer mejor término desde e-class

**Tests (todos pasan)**:
```
x + 0           → x          ✓
x * 1           → x          ✓
(x + 0) * 1     → x          ✓
(x + y) * 0     → 0          ✓
x*1 + 0         → x          ✓ (1 iteración)
x * (y + z)     → explorado   ✓ (2 iteraciones, 8 nodos)
```

**API de uso**:
```lean
import AmoLean.EGraph.Saturate

-- Optimizar con reglas básicas
let result := EGraph.optimizeBasic expr

-- Optimizar con reglas extendidas (distributividad)
let result := EGraph.optimizeExtended expr

-- Optimizar con configuración personalizada
let config := { maxIterations := 50, maxNodes := 5000 }
let (result, satResult) := EGraph.optimize expr rules config
```

---

### Fase 3: Mathlib Extendida sobre E-graph ✓ (COMPLETADA - Enero 2026)

**Objetivo**: Usar teoremas reales de Mathlib como reglas sobre el E-graph.

**Completado**:
- [x] Nuevas reglas desde Mathlib:
  - Conmutatividad: `addComm`, `mulComm` (2 reglas)
  - Asociatividad: `addAssocRight`, `addAssocLeft`, `mulAssocRight`, `mulAssocLeft` (4 reglas)
- [x] Colecciones de reglas: `commRules`, `assocRules`, `semiringRules` (15 reglas total)
- [x] Funciones helper en `MathlibToEGraph`:
  - `commPattern`, `assocPattern`, `identityPattern`
  - `mathlibCommRules`, `mathlibAssocRules`, `mathlibIdentityRules`
- [x] Optimización en `applyRuleAt`: evita merges redundantes
- [x] Configuración ajustada para evitar explosión de E-graph
- [x] **Macro `#compile_rules`** - Extracción automática de reglas desde teoremas
  - Convierte `Lean.Expr` a `Pattern` usando metaprogramación
  - Soporta `Add.add`, `HAdd.hAdd`, `Mul.mul`, `HMul.hMul`, `OfNat.ofNat`
  - Archivo: `AmoLean/Meta/CompileRules.lean`
- [x] **Auditoría de Generalidad** - Verificado soporte de Type Classes
  - 10 teoremas genéricos compilados exitosamente
  - Soporta AddCommMagma, MulOneClass, LeftDistribClass, etc.
  - NO limitada a tipos concretos
  - Archivo: `Tests/GenericsAudit.lean`

**NOTA sobre conmutatividad/asociatividad**:
Las reglas de comm/assoc pueden causar explosión del E-graph. Usar siempre con límites bajos:
```lean
let config := { maxIterations := 3, maxNodes := 50 }
let result := optimizeSemiring expr config
```

---

### Fase 4: Extensión de Potencias + Campos Finitos ✓ (COMPLETADA - Enero 2026)

**Objetivo**: Añadir potencias al AST y explorar ZMod.

**Completado**:
- [x] Constructor `pow` añadido al AST
- [x] Integración con E-graph y CodeGen
- [x] ZMod funcionando con reglas genéricas
- [x] Exploración de teoremas de característica

---

## Fase 5: FFT/NTT - Diseño Vectorial (EN PROGRESO)

### 5.0 Diagnóstico de Problemas Pre-Fase 5

Antes de implementar FFT, identificamos tres problemas críticos que el diseño actual no puede manejar:

#### A. La "Trampa Escalar" (Scalar Trap)

**Problema**: El AST actual `Expr α` es escalar:
```lean
inductive Expr (α : Type) where
  | const : α → Expr α
  | var : VarId → Expr α
  | add : Expr α → Expr α → Expr α
  | mul : Expr α → Expr α → Expr α
  | pow : Expr α → Nat → Expr α
```

Una FFT no opera sobre un número, sino sobre un **vector de N elementos** (típicamente N = 2^20 = 1,048,576).

**Riesgo**: Si intentamos modelar una FFT desenrollando el bucle en el AST actual, generaremos un árbol de ~millones de nodos. El E-Graph colapsará por consumo de memoria.

**Síntoma esperado**: "Out of Memory" o tiempos de compilación infinitos.

#### B. La Explosión de las Potencias

**Problema**: Las reglas de potencia (`pow_add`, `pow_mul`, `zmod_pow_card`) crean muchas formas equivalentes muy rápidamente.

**Ejemplo**: `x^10` puede representarse como:
- `x * x * x * x * x * x * x * x * x * x`
- `(x^2)^5`
- `(x^5)^2`
- `x^2 * x^8`
- ... (exponencialmente muchas formas)

**Riesgo**: El espacio de búsqueda crece exponencialmente. El E-Graph se "inunda" de nodos inútiles.

**Mitigación propuesta**: Ajustar `CostModel` para penalizar severamente las expansiones de potencias.

#### C. Inferencia de Tipos Dependientes

**Problema**: `ZMod n` depende del valor `n`.

**Riesgo**: Al escalar a operaciones complejas, la macro `#compile_rules` podría fallar al intentar inferir `n` si este no es explícito en el contexto, generando reglas que no hacen match.

**Mitigación propuesta**: Usar tipos dependientes con `n` explícito en el tipo.

---

### 5.1 Fundamentos Teóricos

El diseño de Fase 5 se basa en cuatro fuentes académicas clave:

#### Fuente 1: SPIRAL - Productos Kronecker (Franchetti et al.)

**Paper**: "Efficient SIMD Vectorization for Hashing in OpenSSL" y literatura SPIRAL

**Concepto clave**: Representar transformadas (FFT, DCT, etc.) usando **productos Kronecker** en lugar de operaciones escalares:

```
DFT_{mn} = (DFT_m ⊗ I_n) · T^{mn}_n · (I_m ⊗ DFT_n) · L^{mn}_m
```

Donde:
- `⊗` es el producto Kronecker (tensor product)
- `I_n` es la matriz identidad n×n
- `T^{mn}_n` son los "twiddle factors" (raíces de unidad)
- `L^{mn}_m` es la permutación stride

**Por qué esto resuelve la Trampa Escalar**:

> "Symbolic vectorization of DSP transforms translates the problem of vectorizing DSP transform algorithms into the problem of generating efficient scalar code for DSP transforms." — Franchetti et al.

El E-graph opera sobre fórmulas Kronecker (O(log N) nodos), no sobre expresiones escalares expandidas (O(N) nodos).

**Reglas de reescritura a nivel Kronecker**:
```
(I_m ⊗ A) · (I_m ⊗ B) = I_m ⊗ (A · B)           -- fusión
L^{mn}_n · (A_m ⊗ B_n) · L^{mn}_m = B_n ⊗ A_m   -- conmutación
L^{kmn}_n = (L^{kn}_n ⊗ I_m) · (I_k ⊗ L^{mn}_n) -- factorización stride
```

#### Fuente 2: High Performance SIMD Modular Arithmetic (Fortin et al.)

**Paper**: "High-performance SIMD modular arithmetic for polynomial evaluation"

**Concepto clave**: Para primos p ≤ 50 bits, usar representación de punto flotante con FMA (Fused Multiply-Add):

```c
// Multiplicación modular vía FMA
double h = x * y;
double l = fma(x, y, -h);     // Error-free transformation
double b = h * (1.0/p);
double c = floor(b);
double result = fma(-c, p, h) + l;
```

**Resultados reportados**:
> "This FP-based algorithm with FMAs enables us to obtain SIMD speedups of up to 3.7x on AVX2, and up to 7.2x on AVX-512."

**Aplicación a AMO-Lean**: Generar código SIMD eficiente para aritmética en `ZMod p`.

#### Fuente 3: Dependent Types in Practical Programming (Xi & Pfenning)

**Paper**: "Dependent Types in Practical Programming" (POPL 1999)

**Concepto clave**: Codificar la longitud de estructuras de datos en el tipo:

```ml
datatype 'a list = nil | cons of 'a * 'a list
typeref 'a list of nat with
    nil <| 'a list(0)
  | cons <| {n:nat} 'a * 'a list(n) -> 'a list(n+1)
```

**Beneficio - Eliminación estática de bounds checking**:
> "sub <| {n:nat} {i:nat | i < n} 'a array(n) * int(i) -> 'a"
> — El acceso fuera de límites es *imposible* por construcción de tipos.

**Tipos existenciales para longitudes desconocidas**:
```ml
filter : ('a -> bool) -> {n:nat} 'a list(n) -> [m:nat | m<=n] 'a list(m)
```

**Aplicación a AMO-Lean**: Definir `VecExpr α n` donde `n` es la longitud, garantizando seguridad de memoria por construcción.

#### Fuente 4: Dependently-Typed Formalisation of Typed Term Graphs (Kahl)

**Paper**: "Dependently-Typed Formalisation of Typed Term Graphs"

**Concepto clave**: Representar grafos de términos con tipos en las aristas:

```agda
record CodeGraph {m n : ℕ} (inTypes : Vec Type m) (outTypes : Vec Type n) : Set₁ where
  field Inner : Set
        iType : Inner → Type
  Node = Fin m ⊎ Inner
  nType : Node → Type
  ...
```

**Aplicación a AMO-Lean**: Si extendemos el E-graph para tener tipos en las e-classes, podemos verificar corrección de tipos durante la saturación.

---

### 5.2 Arquitectura Propuesta: Sistema de Tres Niveles

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     NIVEL ALTO: MatExpr                                 │
│  • Productos Kronecker (⊗)                                              │
│  • Permutaciones simbólicas (L, stride, bit-reversal)                   │
│  • Transformadas simbólicas (DFT_n, NTT_n)                             │
│  • E-graph opera aquí: O(log N) nodos                                  │
├─────────────────────────────────────────────────────────────────────────┤
│                     NIVEL MEDIO: VecExpr α n                            │
│  • Vectores con longitud en el tipo                                     │
│  • Operaciones: map, zip, split, concat, interleave                    │
│  • Garantía de seguridad de memoria por tipos dependientes             │
├─────────────────────────────────────────────────────────────────────────┤
│                     NIVEL BAJO: Expr α (existente)                      │
│  • Expresiones escalares                                                │
│  • Solo para kernels pequeños (DFT₂, butterfly)                        │
│  • CodeGen a C/SIMD intrinsics                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

**Flujo de datos**:
```
MatExpr (Kronecker)
    │
    │ saturate + extract
    ▼
MatExpr optimizado
    │
    │ lower (expandir a bucles + kernels)
    ▼
VecExpr α n
    │
    │ unroll kernels
    ▼
Expr α (para cada kernel pequeño)
    │
    │ exprToC / exprToSIMD
    ▼
C code con SIMD intrinsics
```

---

### 5.3 Diseño de Tipos

#### Vec α n - Vector con longitud en el tipo

```lean
/-- Vector con longitud codificada en el tipo
    Siguiendo DML (Xi & Pfenning) -/
inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
```

**Operaciones con tipos que reflejan la longitud**:
```lean
def append : Vec α m → Vec α n → Vec α (m + n)
def split  : Vec α (m + n) → Vec α m × Vec α n
def head   : Vec α (n + 1) → α                   -- Solo vectores no vacíos
def map    : (α → β) → Vec α n → Vec β n
def zip    : Vec α n → Vec β n → Vec (α × β) n
```

#### VecExpr α n - Expresiones vectoriales

```lean
/-- Expresión que denota un vector de longitud n -/
inductive VecExpr (α : Type) : Nat → Type where
  | lit     : Vec α n → VecExpr α n                           -- Literal
  | var     : VarId → VecExpr α n                             -- Variable vectorial
  | map     : (Expr α → Expr α) → VecExpr α n → VecExpr α n   -- map f v
  | zip     : (Expr α → Expr α → Expr α) →
              VecExpr α n → VecExpr α n → VecExpr α n         -- zipWith f u v
  | split   : VecExpr α (2 * n) → VecExpr α n                 -- primera mitad
  | splitHi : VecExpr α (2 * n) → VecExpr α n                 -- segunda mitad
  | concat  : VecExpr α m → VecExpr α n → VecExpr α (m + n)   -- concatenación
  | interleave : VecExpr α n → VecExpr α n → VecExpr α (2*n)  -- entrelazar
  | stride  : (k : Nat) → VecExpr α (k * n) → VecExpr α (k * n)  -- permutación stride
```

#### MatExpr α m n - Matrices/Transformaciones

```lean
/-- Matriz m × n como transformación lineal -/
inductive MatExpr (α : Type) : Nat → Nat → Type where
  -- Constructores básicos
  | identity  : MatExpr α n n                              -- I_n
  | zero      : MatExpr α m n                              -- matriz cero
  | diag      : VecExpr α n → MatExpr α n n                -- matriz diagonal
  | scalar    : Expr α → MatExpr α 1 1                     -- escalar como 1×1

  -- Transformadas simbólicas (NO expandidas)
  | dft       : (n : Nat) → MatExpr α n n                  -- DFT_n
  | ntt       : (n : Nat) → (p : Nat) → MatExpr α n n      -- NTT_n en Z_p
  | twiddle   : (n k : Nat) → MatExpr α n n                -- T^n_k

  -- Permutaciones
  | perm      : Perm n → MatExpr α n n                     -- permutación

  -- Operaciones de composición
  | kron      : MatExpr α m₁ n₁ → MatExpr α m₂ n₂ →
                MatExpr α (m₁ * m₂) (n₁ * n₂)              -- A ⊗ B (Kronecker)
  | compose   : MatExpr α m k → MatExpr α k n →
                MatExpr α m n                               -- A · B
  | add       : MatExpr α m n → MatExpr α m n →
                MatExpr α m n                               -- A + B
  | smul     : Expr α → MatExpr α m n → MatExpr α m n      -- c · A
```

#### Perm n - Permutaciones simbólicas

```lean
/-- Permutaciones relevantes para FFT -/
inductive Perm : Nat → Type where
  | identity  : Perm n                                      -- Identidad
  | stride    : (m n : Nat) → Perm (m * n)                  -- L^{mn}_n
  | bitRev    : (k : Nat) → Perm (2^k)                      -- Bit-reversal
  | swap      : Perm 2                                       -- Intercambio 2 elementos
  | compose   : Perm n → Perm n → Perm n                    -- P · Q
  | inverse   : Perm n → Perm n                             -- P⁻¹
  | tensor    : Perm m → Perm n → Perm (m * n)              -- P ⊗ Q
```

---

### 5.4 Representación de FFT

#### FFT como fórmula Kronecker

La descomposición Cooley-Tukey se representa directamente:

```lean
/-- FFT de tamaño m*n usando Cooley-Tukey -/
def fftCooleyTukey (m n : Nat) : MatExpr α (m * n) (m * n) :=
  MatExpr.compose
    (MatExpr.kron (MatExpr.dft m) (MatExpr.identity n))    -- (DFT_m ⊗ I_n)
    (MatExpr.compose
      (MatExpr.twiddle (m * n) n)                           -- T^{mn}_n
      (MatExpr.compose
        (MatExpr.kron (MatExpr.identity m) (MatExpr.dft n)) -- (I_m ⊗ DFT_n)
        (MatExpr.perm (Perm.stride m n))))                  -- L^{mn}_m
```

**Conteo de nodos**: Para FFT de tamaño 2^20:
- Con AST escalar: ~1,000,000 nodos (colapsa el E-graph)
- Con Kronecker: ~20 nodos (log₂(2^20) niveles × constante)

#### Kernels base (donde bajamos a Expr)

```lean
/-- DFT₂ (butterfly) - kernel escalar -/
def dft2Matrix : MatExpr α 2 2 :=
  -- [[1, 1], [1, -1]]
  MatExpr.fromRows [
    VecExpr.lit (Vec.cons (Expr.const 1) (Vec.cons (Expr.const 1) Vec.nil)),
    VecExpr.lit (Vec.cons (Expr.const 1) (Vec.cons (Expr.const (-1)) Vec.nil))
  ]

/-- DFT₄ - kernel pequeño -/
def dft4Matrix : MatExpr α 4 4 :=
  -- Radix-4: (DFT₂ ⊗ I₂) · T⁴₂ · (I₂ ⊗ DFT₂) · L⁴₂
  fftCooleyTukey 2 2
```

---

### 5.5 Reglas de Reescritura Kronecker

#### Reglas algebraicas fundamentales

```lean
namespace KroneckerRules

-- Identidad del producto Kronecker
theorem kron_identity : A ⊗ I_1 = A
theorem kron_identity' : I_1 ⊗ A = A

-- Asociatividad (hasta isomorfismo)
theorem kron_assoc : (A ⊗ B) ⊗ C ≃ A ⊗ (B ⊗ C)

-- Compatibilidad con composición
theorem kron_compose : (A ⊗ B) · (C ⊗ D) = (A · C) ⊗ (B · D)
  -- cuando las dimensiones son compatibles

-- Fusión de identidades
theorem kron_id_compose : (I_m ⊗ A) · (I_m ⊗ B) = I_m ⊗ (A · B)
theorem kron_compose_id : (A ⊗ I_n) · (B ⊗ I_n) = (A · B) ⊗ I_n

-- Conmutación con stride
theorem stride_commute : L^{mn}_n · (A_m ⊗ B_n) · L^{mn}_m = B_n ⊗ A_m

-- Factorización de stride
theorem stride_factor : L^{kmn}_n = (L^{kn}_n ⊗ I_m) · (I_k ⊗ L^{mn}_n)

-- Stride identity
theorem stride_self_inverse : L^{mn}_n · L^{mn}_m = I_{mn}

-- Diagonal y Kronecker
theorem diag_kron : diag(a) ⊗ diag(b) = diag(a ⊗ b)

end KroneckerRules
```

#### Reglas de vectorización SIMD

```lean
namespace SIMDRules

-- El constructo A ⊗ I_ν (donde ν = ancho SIMD) se vectoriza trivialmente
-- Cada operación escalar → operación SIMD
theorem vectorize_add : (add ⊗ I_ν) = simd_add
theorem vectorize_mul : (mul ⊗ I_ν) = simd_mul

-- Permutaciones que mapean a instrucciones SIMD específicas
-- L^{2ν}_ν → unpacklo/unpackhi
theorem stride_to_shuffle : L^{2ν}_ν = shuffle_instr

end SIMDRules
```

#### Reglas específicas de FFT

```lean
namespace FFTRules

-- Cooley-Tukey canónico
theorem ct_decomp :
  DFT_{mn} = (DFT_m ⊗ I_n) · T^{mn}_n · (I_m ⊗ DFT_n) · L^{mn}_m

-- Casos base
theorem dft_1 : DFT_1 = I_1
theorem dft_2 : DFT_2 = [[1, 1], [1, -1]]

-- Radix-4 (más eficiente en práctica)
theorem radix_4 :
  DFT_{4m} = (DFT_4 ⊗ I_m) · T^{4m}_m · (I_4 ⊗ DFT_m) · L^{4m}_4

-- Propiedad de inversión
theorem dft_inverse : DFT_n · (1/n) · DFT_n^* = I_n

-- Para NTT (Number Theoretic Transform)
theorem ntt_over_zmod :
  NTT_n [ZMod p] = DFT_n donde ω = primitiveRoot p n

end FFTRules
```

---

### 5.6 Operaciones SIMD sobre ZMod p

#### Representación dual

```lean
/-- Representación de elemento en ZMod p
    - exact: representación exacta para verificación
    - simd: representación FP para código SIMD -/
structure ZModRepr (p : Nat) where
  exact : ZMod p
  simd  : Float  -- Para generación de código SIMD

/-- Vector en ZMod p con longitud en el tipo -/
def ZModVec (p : Nat) (n : Nat) := VecExpr (ZMod p) n
```

#### Aritmética modular SIMD (de Fortin et al.)

Para primos p ≤ 50 bits, generamos código usando FMA:

```lean
/-- Multiplicación modular via FMA (generación de código)
    Implementa el algoritmo de Fortin et al. -/
def genMulModFMA (p : Nat) : String :=
  s!"
  // Multiplicación modular para p = {p}
  double mulmod(double x, double y) {
    double h = x * y;
    double l = fma(x, y, -h);           // Error-free transformation
    double b = h * {1.0 / p.toFloat};   // Precomputado: 1/p
    double c = floor(b);
    double d = fma(-c, {p.toFloat}, h);
    return d + l;                        // Resultado en [0, 2p)
  }
  "
```

#### Twiddle factors precomputados

```lean
/-- Precomputar ω^k para k = 0..n-1 donde ω es raíz n-ésima en ZMod p -/
def twiddleFactors (p n : Nat) (ω : ZMod p) : ZModVec p n :=
  VecExpr.lit (Vec.ofFn (fun k => ω ^ k.val))
```

---

### 5.7 Extensión del E-Graph

#### Nuevos nodos

```lean
inductive ENodeOp where
  -- Existentes (nivel escalar)
  | const : Int → ENodeOp
  | var   : VarId → ENodeOp
  | add   : ENodeOp
  | mul   : ENodeOp
  | pow   : Nat → ENodeOp

  -- Nuevos (nivel vectorial)
  | vec        : Nat → ENodeOp           -- vector de n elementos
  | identity   : Nat → ENodeOp           -- I_n
  | dft        : Nat → ENodeOp           -- DFT_n simbólico
  | ntt        : Nat → Nat → ENodeOp     -- NTT_n en Z_p
  | twiddle    : Nat → Nat → ENodeOp     -- T^n_k
  | kron       : ENodeOp                  -- ⊗
  | matCompose : ENodeOp                  -- ·
  | perm       : PermId → ENodeOp        -- permutación
  | stride     : Nat → Nat → ENodeOp     -- L^{mn}_n
```

#### Nuevo CostModel

```lean
structure VectorCostModel where
  -- Costos base
  simdWidth     : Nat := 4      -- ancho SIMD (4 para AVX, 8 para AVX-512)
  addCost       : Nat := 1
  mulCost       : Nat := 1
  fmaCost       : Nat := 1      -- FMA cuenta como 1, no 2
  shuffleCost   : Nat := 2      -- permutaciones tienen costo
  memoryCost    : Nat := 10     -- acceso a memoria es caro

  -- Costos Kronecker
  kronCost      : Nat := 0      -- ⊗ es simbólico, no tiene costo directo
  dftSymbolic   : Nat := 0      -- DFT_n simbólico no tiene costo
  dft2Kernel    : Nat := 4      -- DFT₂ expandido: 2 add + 2 sub
  dft4Kernel    : Nat := 16     -- DFT₄ expandido

  -- Penalizaciones
  scalarPenalty : Nat := 1000   -- penalizar expansión escalar
```

---

### 5.8 Impacto en CodeGen

#### Estrategia de lowering en dos fases

```
Fase 1: MatExpr → Lista de operaciones vectoriales
Fase 2: Operaciones vectoriales → C con SIMD intrinsics
```

#### Ejemplo de código generado

Para `DFT_8`:

```c
// Generado por AMO-Lean Phase 5
#include <immintrin.h>

void fft8_avx(double* restrict in, double* restrict out) {
    // Cargar datos
    __m256d x0 = _mm256_load_pd(&in[0]);
    __m256d x1 = _mm256_load_pd(&in[4]);

    // Nivel 1: DFT₂ ⊗ I₄ (4 butterflies en paralelo)
    __m256d t0 = _mm256_add_pd(x0, x1);
    __m256d t1 = _mm256_sub_pd(x0, x1);

    // Twiddle factors (precomputados)
    __m256d tw = _mm256_set_pd(w3, w2, w1, w0);
    t1 = _mm256_mul_pd(t1, tw);

    // Nivel 2: I₂ ⊗ DFT₂, con shuffle
    __m256d u0 = _mm256_unpacklo_pd(t0, t1);
    __m256d u1 = _mm256_unpackhi_pd(t0, t1);

    __m256d y0 = _mm256_add_pd(u0, u1);
    __m256d y1 = _mm256_sub_pd(u0, u1);

    // Almacenar resultado
    _mm256_store_pd(&out[0], y0);
    _mm256_store_pd(&out[4], y1);
}
```

---

### 5.9 Plan de Implementación

| Subfase | Descripción | Archivos | Dependencias | Estado |
|---------|-------------|----------|--------------|--------|
| **5.1** | `Vec α n` básico | `AmoLean/Vector/Basic.lean` | Ninguna | ✓ DONE |
| **5.2** | `VecExpr α n` y `MatExpr` | `AmoLean/Matrix/Basic.lean` | 5.1 | ✓ DONE |
| **5.3** | `Perm n` y permutaciones | `AmoLean/Matrix/Perm.lean` | 5.2 | ✓ DONE |
| **5.4** | Extensión E-graph para Kronecker | `AmoLean/EGraph/Vector.lean` | 5.2, 5.3 | ✓ DONE |
| **5.5** | Sigma-SPL IR & Lowering | `AmoLean/Sigma/Basic.lean` | 5.4 | ✓ DONE |
| **5.6** | Kernel Expansion (DFT₂ → scalar ops) | `AmoLean/Sigma/Expand.lean` | 5.5 | ✓ DONE |
| **5.7** | CodeGen (SigmaExpr → C code) | `AmoLean/Sigma/CodeGen.lean` | 5.6 | ✓ DONE |
| **5.8** | SIMD CodeGen (AVX intrinsics) | `AmoLean/Sigma/SIMD.lean` | 5.7 | ✓ DONE |
| **5.9** | ZMod SIMD con FMA | `AmoLean/Sigma/ZModSIMD.lean` | 5.8 | ✓ DONE |
| **5.10** | Pruebas de corrección | `AmoLean/Sigma/Correctness.lean` | 5.1-5.9 | Pendiente |

### Resumen de Pruebas Fase 5

**Estado de Pruebas por Módulo:**
| Módulo | Archivo | Pruebas | Pasadas | Estado |
|--------|---------|---------|---------|--------|
| Perm eval | Matrix/Perm.lean | 4 | 4 | ✓ |
| MatEGraph | EGraph/Vector.lean | 5 | 5 | ✓ |
| Sigma-SPL | Sigma/Basic.lean | 5 | 5 | ✓ |
| Expand | Sigma/Expand.lean | 5 | 5 | ✓ |
| CodeGen | Sigma/CodeGen.lean | 5 | 5 | ✓ |
| SIMD | Sigma/SIMD.lean | 3 | 3 | ✓ |
| ZModSIMD | Sigma/ZModSIMD.lean | 3 | 3 | ✓ |
| **Total** | | **30** | **30** | **100%** |

**Benchmarks Clave:**
- MatEGraph: FFT Cooley-Tukey DFT_8 representado con 11 nodos (vs ~64 escalar)
- Expansión: DFT_4 produce 8 operaciones (4 adds, 4 subs) - O(N log N)
- SIMD: DFT_4 in-register con 10 instrucciones AVX
- ZMod: NTT_4 completo con aritmética modular FMA

**Líneas de Código Fase 5:** ~3,030 líneas en 9 módulos

---

### 5.10 Riesgos y Mitigaciones

| Riesgo | Probabilidad | Impacto | Mitigación |
|--------|--------------|---------|------------|
| Tipos dependientes complejos en Lean4 | Media | Alto | Empezar con `n` explícito, no inferido |
| E-matching sobre Kronecker lento | Media | Medio | Limitar profundidad de ⊗ anidados |
| Integración con ZMod de Mathlib | Baja | Medio | Usar representación dual (exacta + SIMD) |
| CodeGen SIMD complejo | Media | Medio | Empezar con AVX2, expandir después |
| Proofs de corrección para Kronecker | Alta | Alto | Incrementalmente, empezando por identidades |

---

### Fase 5.10: Verificación ✓ (COMPLETADA - Enero 2026)

**Objetivo**: Verificar corrección del pipeline completo.

**Completado**:
- [x] `AmoLean/Verification/Semantics.lean`: Semántica de referencia para SigmaExpr
- [x] `AmoLean/Verification/FuzzTest.lean`: Testing diferencial property-based
- [x] `AmoLean/Verification/Theorems.lean`: Teoremas formales de corrección
- [x] Pruebas para DFT_4, identidades de Kronecker, expansión de kernels

**Resultado**: Pipeline Phase 5 completamente verificado.

---

### Fase 6: FRI Protocol ✓ (EN PROGRESO - Enero 2026)

**Objetivo**: Implementar el protocolo FRI (Fast Reed-Solomon IOP of Proximity) como caso de estudio.

#### 6.1 Infraestructura ✓ (COMPLETADA)
- [x] `AmoLean/FRI/Basic.lean`: Tipos core, ZKCostModel, FieldConfig
- [x] NodeTransparency, FRIParams, TileConfig

#### 6.2 FRI Fold ✓ (COMPLETADA)
- [x] `AmoLean/FRI/Fold.lean`: friFold con tipos dependientes
- [x] `AmoLean/FRI/Kernel.lean`: FRILayerKernel parametrizado

#### 6.3 Transcript & Cryptographic Intrinsics ✓ (COMPLETADA)
- [x] `AmoLean/FRI/Transcript.lean`: TranscriptState, CryptoSigma
- [x] Intrinsic operations: absorb, squeeze, hash, merkleHash, domainEnter/Exit

#### 6.4 Vectorized Merkle Tree ✓ (COMPLETADA)
- [x] `AmoLean/FRI/Merkle.lean`: FlatMerkle, MerkleProof
- [x] Leaves-first layout, bottom-up construction

#### 6.5 FRI Protocol State Machine ✓ (COMPLETADA)
- [x] `AmoLean/FRI/Protocol.lean`: RoundState, friRound, multi-round execution
- [x] `Benchmarks/FRI_Flow.lean`: Integration test con flow pattern verification

#### 6.6-7: Plan Reordenado (ADR-008)

**Decisión Estratégica**: Reordenar fases para evitar "verificación en el vacío".

*Riesgo Identificado*: Verificar formalmente código Lean sin generar C podría probar
teoremas sobre estructuras que no funcionan en la práctica (memoria, alineación AVX, etc.)

*Plan Modificado*:
```
Original:  6.5 → 6.6 (Verificación) → 7 (CodeGen)
Nuevo:     6.5 → 7-Alpha (CodeGen) → 7-Beta (DiffFuzz) → 6.6 (Verificación)
```

#### 7-Alpha: FRI CodeGen → C ✓ (COMPLETADA - Enero 2026)
- [x] `AmoLean/FRI/CodeGen.lean`: CryptoSigma → C con proof anchors (~710 líneas)
- [x] `generated/fri_protocol.c`: FRI completo (~320 líneas)
- [x] Proof anchors: comentarios estructurados documentando pre/postcondiciones

#### 7-Beta: Differential Fuzzing ✓ (COMPLETADA - Enero 2026)
- [x] `Benchmarks/FRI_DiffTest.lean`: Testing comparativo (~350 líneas)
- [x] Lean evaluator vs C binary - comparación bit a bit
- [x] **BUG CRÍTICO ENCONTRADO Y CORREGIDO**: Buffer swap logic error

**Bug encontrado**: El código C retornaba P1 (resultado de round 0) en lugar de P2 (resultado de round 1).
- Causa: Swap condicional `if (round + 1 < num_rounds)` omitía el swap del último round
- Efecto: `current` apuntaba a datos viejos mientras `next` tenía el resultado correcto
- Fix: Swap incondicional después de cada round

Este bug demuestra el valor del fuzzing diferencial: el código compilaba, no crasheaba, y los valores intermedios (commitments, challenges) eran correctos. Solo el valor final estaba corrupto.

#### 6.6: Verificación Formal con Proof Anchors ✓ (COMPLETADA - Enero 2026)
- [x] `AmoLean/Verification/FRI_Properties.lean`: Teoremas formales (~350 líneas)
- [x] `friFold_spec`: Especificación del fold verificada
- [x] `round_ordering_secure`: Ordenamiento Fiat-Shamir verificado
- [x] `domain_size_after_rounds`: Reducción de dominio verificada
- [x] Correspondencia proof anchors ↔ teoremas documentada
- [x] `docs/FINAL_REPORT.md`: Reporte final del proyecto

**PROYECTO FASE 6 COMPLETADO** - Todas las fases hasta 6.6 finalizadas.

---

### Fase Poseidon: Non-Linear Extensions (EN PROGRESO - Enero 2026)

**Objetivo**: Extender AMO-Lean para soportar operaciones no-lineales, habilitando Poseidon2 hash.

**Documentación detallada**: Ver `docs/poseidon/` para ADRs y progreso.

#### Estado de Implementación

| Paso | Descripción | Estado |
|------|-------------|--------|
| 0 | Prerrequisitos (ZModSIMD) | Parcial |
| 0.5 | Especificación ejecutable | ✓ Completado |
| 1 | Extensión IR (elemwise) | ✓ Completado |
| 1.5 | Sanity Tests | ✓ Completado (4/4 pasan) |
| 2 | CodeGen SIMD | Pendiente |
| 3 | Poseidon2 en MatExpr | Pendiente |
| 4 | Verificación | Pendiente |
| 5 | Integración MerkleTree | Pendiente |

#### Paso 1: Extensión del IR ✓ (COMPLETADO)

**Implementado**:
- [x] `ElemOp` type: `pow`, `custom`
- [x] `elemwise` constructor en MatExpr
- [x] `head`/`tail` en VecExpr para rondas parciales
- [x] E-Graph con barrera opaca (arquitectónica)
- [x] Lowering de elemwise a SigmaExpr con kernel `sbox`
- [x] Evaluador semántico para sbox

**Archivos modificados**:
- `AmoLean/Matrix/Basic.lean` - ElemOp, elemwise
- `AmoLean/Vector/Basic.lean` - head/tail
- `AmoLean/EGraph/Vector.lean` - MatEGraph
- `AmoLean/Sigma/Basic.lean` - sbox kernel
- `AmoLean/Sigma/Expand.lean` - square chain
- `AmoLean/Verification/Semantics.lean` - evaluador

#### Paso 1.5: Sanity Tests ✓ (COMPLETADO)

**Tests implementados** (`Tests/ElemwiseSanity.lean`):
1. **Semantic Check**: sbox5 (x^5 mod p) computa correctamente
2. **Optimization Check**: E-Graph requiere regla explícita para composición
3. **Safety Check (CRÍTICO)**: E-Graph NO prueba (A+B)^2 = A^2+B^2
4. **Barrier Integrity**: elemwise no distribuye sobre adición

**Resultado**: 4/4 tests pasan - Safe to proceed to CodeGen

#### Problemas Encontrados y Soluciones

| Problema | Solución |
|----------|----------|
| Sintaxis `let open` no soportada | Usar `open` a nivel de módulo |
| Axioma sorry bloquea `#eval` | Usar `#eval!` |
| Cálculo incorrecto 5^5 mod 17 | Recalculado: 3125 mod 17 = 14 |

---

## Estructura del Proyecto (Actualizada para Fase 6)

```
amo-lean/
├── AmoLean.lean                 # Módulo principal, API pública
├── AmoLean/
│   ├── Basic.lean               # AST escalar, reglas, motor greedy
│   ├── Correctness.lean         # Pruebas de corrección escalares
│   ├── MathlibIntegration.lean  # Integración con Mathlib
│   ├── CodeGen.lean             # Generación de código C escalar
│   ├── Meta/
│   │   └── CompileRules.lean    # #compile_rules macro
│   ├── EGraph/
│   │   ├── Basic.lean           # E-graph core
│   │   ├── EMatch.lean          # E-matching
│   │   ├── Saturate.lean        # Saturación
│   │   └── Vector.lean          # [✓ 5.4] E-graph para Kronecker
│   ├── Vector/                  # [✓ 5.1]
│   │   └── Basic.lean           # Vec α n, VecExpr α n
│   ├── Matrix/                  # [✓ 5.2, 5.3]
│   │   ├── Basic.lean           # MatExpr α m n, Perm n
│   │   └── Perm.lean            # Evaluación de permutaciones
│   ├── Sigma/                   # [✓ 5.5-5.9]
│   │   ├── Basic.lean           # SigmaExpr, Lowering
│   │   ├── Expand.lean          # Kernel expansion
│   │   ├── CodeGen.lean         # SigmaExpr → C code
│   │   ├── SIMD.lean            # AVX intrinsics generation
│   │   └── ZModSIMD.lean        # Modular arithmetic SIMD
│   ├── Verification/            # [✓ 5.10]
│   │   ├── Semantics.lean       # Reference semantics
│   │   ├── FuzzTest.lean        # Differential testing
│   │   └── Theorems.lean        # Formal correctness
│   ├── FRI/                     # [✓ 6.1-6.5, IN PROGRESS 7-Alpha]
│   │   ├── Basic.lean           # [6.1] Core types, ZKCostModel
│   │   ├── Fold.lean            # [6.2] FRI fold with dependent types
│   │   ├── Kernel.lean          # [6.2] FRILayerKernel parametrizado
│   │   ├── Transcript.lean      # [6.3] TranscriptState, CryptoSigma
│   │   ├── Merkle.lean          # [6.4] FlatMerkle, leaves-first
│   │   ├── Protocol.lean        # [6.5] RoundState, friRound
│   │   └── CodeGen.lean         # [7-Alpha] CryptoSigma → C (PRÓXIMO)
│   └── Protocols/               # [Poseidon] Hash protocols
│       └── Poseidon/
│           ├── Spec.lean        # [0.5] Pure specification
│           └── Params/
│               └── BN254.lean   # BN254 parameters
├── Benchmarks/
│   ├── FRI_Fusion.lean          # Fusion benchmark
│   ├── FRI_Symbolic.lean        # Symbolic execution N=8
│   ├── FRI_Flow.lean            # [6.5] Flow pattern verification
│   └── FRI_DiffTest.lean        # [7-Beta] Differential fuzzing (PRÓXIMO)
├── Tests/
│   ├── ZModDemo.lean
│   ├── GenericsAudit.lean
│   └── ElemwiseSanity.lean   # [Poseidon 1.5] Sanity tests
├── docs/
│   ├── PROJECT_STATUS.md
│   ├── ESTADO_PROYECTO.md
│   └── optimizaciones prefase5/ # Papers de referencia
├── ROADMAP.md                   # Este archivo
└── lakefile.lean
```

---

## Lecciones Aprendidas

### De la Fase 1.75 (Benchmark)
- **Greedy es rápido pero limitado**: 253k nodos en 0.5s, pero no explora alternativas
- **Asociatividad rompe greedy**: 70x slowdown porque aplica reglas indefinidamente
- **Cost model es esencial**: Sin él, no hay criterio de "mejor"

### De la Fase 2 (E-graph)
- **Estructuras planas funcionan**: `Array` + `HashMap` evitan problemas de GC
- **Rebuild es crítico**: Sin re-canonicalización, el hashcons queda inconsistente
- **E-matching es elegante**: Patrones + sustituciones = búsqueda declarativa

### De egg (Willsey et al.)
- **Rebuilding**: Diferir mantenimiento de invariantes mejora rendimiento 88×
- **E-class analysis**: Framework general para integrar análisis semántico
- **Separation of phases**: Read phase → Write phase → Rebuild

### De Fiat-Crypto Rewriter (Gross et al.)
- **PHOAS**: Evita bookkeeping de binders
- **Let-lifting**: Crucial para evitar explosión de memoria
- **Pattern compilation**: Seguir Maranget para eficiencia

### De SPIRAL (Franchetti et al.)
- **Productos Kronecker**: Permiten representación compacta de FFT
- **Vectorización simbólica**: No expandir a escalares, mantener nivel alto
- **Reglas algebraicas**: Las identidades Kronecker guían la optimización

### De DML (Xi & Pfenning)
- **Longitud en el tipo**: Elimina bounds checking por construcción
- **Tipos existenciales**: Manejan longitudes desconocidas estáticamente
- **Separar índices de términos**: Los índices son "puros", sin efectos

---

## Referencias

1. Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. Sun et al. "E-Graphs as Circuits, and Optimal Extraction via Treewidth" (2024)
3. Gross et al. "Accelerating Verified-Compiler Development with a Verified Rewriting Engine" (ITP 2022)
4. Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic" (Fiat-Crypto)
5. Metaprogramming in Lean 4 (documentación oficial)
6. Franchetti et al. "SPIRAL: Code Generation for DSP Transforms" (Proceedings of the IEEE, 2005)
7. Franchetti et al. "Efficient SIMD Vectorization for Hashing in OpenSSL" (2024)
8. Fortin et al. "High-performance SIMD modular arithmetic for polynomial evaluation" (2024)
9. Xi & Pfenning "Dependent Types in Practical Programming" (POPL 1999)
10. Kahl "Dependently-Typed Formalisation of Typed Term Graphs"

---

*Documento actualizado: Enero 26, 2026*
*Estado: Fase 6 Completada. Fase Poseidon Paso 1 Completado - Ready for CodeGen.*
*Ver: docs/FINAL_REPORT.md para reporte de Fase 6.*
*Ver: docs/poseidon/PROGRESS.md para progreso de Fase Poseidon.*
