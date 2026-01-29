# Fase 6A: AMO-Lean como Verificador de Plonky3

**Fecha de creación**: 2026-01-29
**Estado**: COMPLETADO
**Prerrequisito**: Fase 5 NTT Core completada

---

## RESULTADOS DE VERIFICACIÓN

### Resumen Ejecutivo

| Fase | Estado | Resultado |
|------|--------|-----------|
| 6A.1 Análisis Plonky3 | ✅ COMPLETADO | 100% compatibilidad confirmada |
| 6A.2 Rust Shim | ✅ COMPLETADO | 9 símbolos exportados, 28/28 tests |
| 6A.3 Detección de Orden | ✅ COMPLETADO | MATCH - Ambos usan RN (bit-reverse input, natural output) |
| 6A.4 Oracle Tests | ✅ COMPLETADO | **64/64 tests PASSED (100%)** |
| 6A.5 Benchmark | ✅ COMPLETADO | Plonky3 ~2x más rápido (esperado) |

### Resultados Oracle Tests (6A.4)

```
═══════════════════════════════════════════════════════════════
  FINAL RESULTS
═══════════════════════════════════════════════════════════════
  Total tests:  64
  Passed:       64
  Failed:       0
  Success rate: 100.0%
═══════════════════════════════════════════════════════════════

  *** ALL TESTS PASSED ***
  Plonky3 and AMO-Lean produce IDENTICAL NTT results!
```

### Tamaños Verificados

| N | log₂(N) | omega | Sequential | Zeros | Ones | Impulse | Max | Random (50) | Roundtrip |
|---|---------|-------|------------|-------|------|---------|-----|-------------|-----------|
| 8 | 3 | 0xFFFFFFFEFF000001 | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| 16 | 4 | 0xEFFFFFFF00000001 | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| 32 | 5 | 0x00003FFFFFFFC000 | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| 64 | 6 | 0x0000008000000000 | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| 128 | 7 | 0xF80007FF08000001 | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| 256 | 8 | 0xBF79143CE60CA966 | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| 512 | 9 | 0x1905D02A5C411F4E | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| 1024 | 10 | 0x9D8F2AD78BFED972 | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |

### Resultados Benchmark (6A.5)

```
═══════════════════════════════════════════════════════════════════════
  BENCHMARK RESULTS
═══════════════════════════════════════════════════════════════════════

┌──────────┬─────────────────────┬─────────────────────┬────────────────┐
│   Size   │   Plonky3 (us)      │   AMO-Lean (us)     │     Ratio      │
├──────────┼─────────────────────┼─────────────────────┼────────────────┤
│ N=256    │      4.9 ± 0.9     │      9.4 ± 1.0     │ 1.90x Plonky3  │
│ N=512    │      9.5 ± 0.7     │     16.4 ± 1.2     │ 1.72x Plonky3  │
│ N=1024   │     15.4 ± 1.1     │     29.6 ± 1.8     │ 1.92x Plonky3  │
│ N=2048   │     29.8 ± 1.6     │     62.9 ± 2.8     │ 2.11x Plonky3  │
│ N=4096   │     63.2 ± 2.0     │    135.3 ± 4.1     │ 2.14x Plonky3  │
│ N=8192   │    132.9 ± 4.2     │    319.9 ± 7.7     │ 2.41x Plonky3  │
│ N=16384  │    281.2 ± 7.6     │    637.5 ± 14.8    │ 2.27x Plonky3  │
│ N=32768  │    636.5 ± 14.8    │   1361.2 ± 25.7    │ 2.14x Plonky3  │
│ N=65536  │   1396.2 ± 33.0    │   2907.5 ± 54.0    │ 2.08x Plonky3  │
└──────────┴─────────────────────┴─────────────────────┴────────────────┘

  Average: Plonky3 is 2.08x faster than AMO-Lean
```

### Análisis de Rendimiento

| Factor | Plonky3 | AMO-Lean | Impacto |
|--------|---------|----------|---------|
| Twiddle caching | Sí (RwLock) | No (on-the-fly) | Plonky3 más rápido |
| SIMD vectorization | AVX2/AVX512 built-in | Separado | Plonky3 más rápido |
| Verificación formal | No | Sí (Lean 4) | AMO-Lean más seguro |
| Lazy reduction | No | Sí (Harvey 2014) | - |

**Interpretación**: La diferencia de ~2x es esperada y aceptable:
- Plonky3 prioriza **rendimiento** para uso en producción
- AMO-Lean prioriza **corrección demostrable** con verificación formal
- AMO-Lean aún tiene rendimiento práctico (~23 M elem/s para N=65536)

### Archivos Generados (Fase 6A.1-6A.5)

```
verification/plonky3/
├── Makefile                    # Build orchestrator
├── README.md                   # Documentation
├── plonky3_shim/              # Rust → C wrapper
│   ├── Cargo.toml             # cdylib + p3-* dependencies
│   └── src/lib.rs             # 9 exported C functions
├── shim_test.c                # Basic shim test (28/28 pass)
├── oracle_test.c              # Full equivalence tests (64/64 pass)
└── benchmark.c                # Performance comparison
```

---

## AUDITORÍA DE ROBUSTEZ EXTREMA (Fase 6A.6)

### Resumen de Hardening

| Test | Estado | Resultado |
|------|--------|-----------|
| FFI Torture Test (1M iter) | ✅ PASS | 0 errores, 3M+ llamadas FFI |
| Panic Safety Audit | ✅ PASS | `panic = "abort"` configurado |
| Deep Fuzzing (120 vectores) | ✅ PASS | 120/120 equivalencia bit-a-bit |
| ABI Layout Audit | ✅ PASS | Todos los offsets idénticos |
| FFI Overhead | ✅ PASS | **0.03%** (< 5% requerido) |

**VEREDICTO: APTO PARA PRODUCCIÓN**

### FFI Torture Test

```
[TEST 1] NTT Roundtrip Stress (1000000 iterations)...
  Completed in 6.92 seconds (289009 calls/sec)
  Errors: 0

[TEST 2] Field Operations Stress (1000000 iterations)...
  Completed in 0.01 seconds (378644453 calls/sec)
  Errors: 0

[TEST 3] Omega Query Stress (100000 iterations)...
  Completed in 0.00 seconds (1005747126 queries/sec)
  Errors: 0

[TEST 4] Varying Size Stress (100000 iterations)...
  Completed in 0.74 seconds
  Errors: 0

TOTAL ERRORS: 0
```

### Panic Safety

```toml
# Cargo.toml verificado
[profile.release]
panic = "abort"  # Previene UB de unwinding across FFI
```

Mecanismos de protección:
- Input validation antes de cualquier operación
- `catch_unwind` envuelve toda la lógica
- `panic = "abort"` como fallback final

### Deep Fuzzing - Vectores Patológicos

| Tipo de Vector | Descripción | Resultado |
|----------------|-------------|-----------|
| Sparse | `[P-1, 0, ..., 0, 1]` | ✅ 8/8 tamaños |
| Geometric | `[1, ω, ω², ω³, ...]` | ✅ 8/8 tamaños |
| Max Entropy | `[P-1, P-2, P-3, ...]` | ✅ 8/8 tamaños |
| Boundary | `[0, 1, P-1, P-2, ...]` | ✅ 8/8 tamaños |
| Alternating | `[0, P-1, 0, P-1, ...]` | ✅ 8/8 tamaños |
| Powers of 2 | `[1, 2, 4, 8, ...]` | ✅ 8/8 tamaños |
| Impulse | `[0, ..., 1, ..., 0]` | ✅ 8/8 tamaños |
| All Max | `[P-1, P-1, ..., P-1]` | ✅ 8/8 tamaños |
| Fibonacci | `[1, 1, 2, 3, 5, ...]` | ✅ 8/8 tamaños |
| Random High | Bits altos aleatorios | ✅ 8/8 tamaños |

**Total: 120/120 PASS (100%)**

### ABI Layout Audit

```
[TEST 1] Structure Size...
  C sizeof(TestLayout):    24 bytes
  Rust size_of::<>():      24 bytes
  [PASS] Sizes match!

[TEST 2] Structure Alignment...
  C _Alignof(TestLayout):  8 bytes
  Rust align_of::<>():     8 bytes
  [PASS] Alignments match!

[TEST 3] Field Offsets...
  Field     | C offset | Rust offset | Match
  ----------|----------|-------------|------
  byte1     |        0 |           0 | YES
  value     |        8 |           8 | YES
  byte2     |       16 |          16 | YES
  [PASS] All offsets match!
```

### FFI Overhead Benchmark

```
  Measurements:
    Pure FFI call (noop):     1.08 ns
    Total NTT (N=256):        3316.79 ns
    Estimated compute time:   3315.70 ns

  FFI Overhead Analysis:
    Overhead / Total:         0.03%

  Verdict:
    [EXCELLENT] FFI overhead is negligible (<1%)
    The current granularity is optimal.
```

### Archivos de Hardening

```
Tests/Plonky3/
├── Hardening/
│   ├── FFI_Stress.c         # 1M iterations stress test
│   ├── PanicTest.c          # Panic safety audit
│   ├── DeepFuzz.c           # 120 pathological vectors
│   ├── LayoutTest.c         # ABI compatibility
│   ├── Makefile             # Build orchestrator
│   └── HARDENING_REPORT.md  # Full report
└── Bench/
    └── FFI_Overhead.c       # FFI call cost measurement
```

---

## Objetivo

Usar AMO-Lean para **verificar formalmente** que la implementación de NTT en Plonky3
produce los mismos resultados que nuestra especificación verificada.

```
┌─────────────────────────────────────────────────────────────────┐
│                    ARQUITECTURA DE VERIFICACIÓN                  │
│                                                                 │
│  Plonky3 (Rust)     cdylib       AMO-Lean (C)                  │
│  ┌─────────────┐  ┌─────────┐   ┌─────────────────────┐        │
│  │ NTT impl    │──│ .so     │───│ ntt_kernel.h        │        │
│  │ Goldilocks  │  │ dlopen  │   │ (verificado Lean)   │        │
│  └─────────────┘  └─────────┘   └─────────────────────┘        │
│        │                                   │                    │
│        └───────────┬───────────────────────┘                    │
│                    ▼                                            │
│             ORACLE TESTING                                      │
│        (vectores random, comparar salida)                       │
└─────────────────────────────────────────────────────────────────┘
```

---

## Decisiones de Diseño

### DD-025: Shared Library (cdylib) en lugar de Static Library

**Problema**: Usar `staticlib` causa conflictos de símbolos (Symbol Clashes):
- Rust incluye sus propios `__rust_alloc`, `memcpy`, etc.
- Conflictos con libc del proyecto C
- Debugging difícil cuando hay símbolos duplicados

**Decisión**: Usar `cdylib` (shared library) con `dlopen/dlsym`:

```rust
// Cargo.toml
[lib]
crate-type = ["cdylib"]
```

```c
// loader.c
void* lib = dlopen("./libplonky3_shim.so", RTLD_NOW);
ntt_fn fn = dlsym(lib, "plonky3_ntt_forward");
```

**Ventajas**:
- Cero conflictos de símbolos (espacios de nombres separados)
- Hot-reload posible (recompilar .so sin recompilar tests)
- Símbolos de Rust completamente aislados

**Desventaja aceptable**: ~1μs overhead por llamada dlsym (irrelevante vs NTT en ms).

---

### DD-026: Makefile Simple en lugar de CMake

**Problema**: CMake no compila Rust nativamente. Integrar Cargo con CMake requiere:
- ExternalProject_Add (frágil)
- corrosion (dependencia extra)
- Scripts complejos

**Decisión**: Usar un Makefile minimalista que orqueste Cargo y GCC:

```makefile
all: libplonky3_shim.so oracle_test

libplonky3_shim.so:
    cd plonky3_shim && cargo build --release
    cp plonky3_shim/target/release/libplonky3_shim.so .

oracle_test: oracle_test.c libplonky3_shim.so
    $(CC) -O3 -o $@ $< -L. -lplonky3_shim -ldl -Wl,-rpath,'$$ORIGIN'
```

**Ventajas**:
- Transparente y debuggeable
- No requiere conocimiento de CMake
- Funciona en Linux y macOS (con ajustes menores)

---

### DD-027: Detector Automático de Orden I/O

**Problema**: Plonky3 puede usar diferentes órdenes de I/O:
- Natural-Natural (NN)
- Natural-BitReverse (NR)
- BitReverse-Natural (RN)
- BitReverse-BitReverse (RR)

**Decisión**: Crear detector automático que prueba las 4 combinaciones:

```c
NTT_Order detect_plonky3_order(size_t n) {
    // 1. Preparar input conocido
    // 2. Ejecutar Plonky3 NTT
    // 3. Comparar con AMO-Lean en cada configuración
    // 4. Retornar la que matchea
}
```

---

## Estructura de Directorios

```
amo-lean/
├── verification/
│   └── plonky3/                    # ← NUEVO
│       ├── Makefile                # Build orchestrator
│       ├── README.md               # Instrucciones
│       ├── plonky3_shim/           # Rust shim (Cargo project)
│       │   ├── Cargo.toml
│       │   └── src/
│       │       └── lib.rs          # extern "C" wrappers
│       ├── order_detector.c        # Detecta orden I/O
│       ├── oracle_test.c           # Tests de equivalencia
│       ├── benchmark.c             # Comparación de performance
│       └── test_vectors/           # Vectores de prueba
│           ├── random_n1024.bin
│           └── edge_cases.bin
└── generated/
    ├── ntt_kernel.h                # Reutilizado
    ├── ntt_skeleton.c              # Reutilizado
    └── field_goldilocks.h          # Reutilizado
```

---

## Subfase 6A.1: Análisis de Plonky3

**Duración estimada**: 1-2 días
**Objetivo**: Entender exactamente cómo Plonky3 implementa NTT para Goldilocks.

### Tareas

| # | Tarea | Criterio de éxito |
|---|-------|-------------------|
| 1.1 | Clonar Plonky3 | `git clone https://github.com/Plonky3/Plonky3` |
| 1.2 | Leer `goldilocks/src/lib.rs` | Documentar representación de campo |
| 1.3 | Leer `dft/src/radix_2_dit.rs` | Documentar algoritmo DIT usado |
| 1.4 | Identificar orden I/O | Determinar si es NN, NR, RN, o RR |
| 1.5 | Identificar Montgomery | Verificar si usa Montgomery representation |
| 1.6 | Identificar twiddle cache | Documentar si precomputa twiddles |

### Preguntas a Responder

1. **¿Qué representación de campo usa?**
   - Standard: `a` stored as `a`
   - Montgomery: `a` stored as `a * R mod p`

2. **¿Qué orden de I/O usa el NTT?**
   - DIT típicamente: input bit-reversed, output natural
   - Pero Plonky3 puede diferir

3. **¿Cómo maneja twiddle factors?**
   - On-the-fly computation
   - Precomputed table
   - Hybrid

4. **¿Qué API expone para NTT Goldilocks?**
   - Trait `TwoAdicSubgroupDft`
   - Funciones concretas

### Entregable

Documento `docs/project/PLONKY3_ANALYSIS.md` con:
- Respuestas a las 4 preguntas
- Código relevante citado
- Diferencias identificadas con AMO-Lean

---

## Subfase 6A.2: Crear plonky3_c_shim

**Duración estimada**: 1 día
**Objetivo**: Crear wrapper Rust que expone Plonky3 como biblioteca C.

### Estructura del Shim

```
plonky3_shim/
├── Cargo.toml
└── src/
    └── lib.rs
```

### Cargo.toml

```toml
[package]
name = "plonky3_shim"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["cdylib"]

[dependencies]
p3-goldilocks = { git = "https://github.com/Plonky3/Plonky3" }
p3-dft = { git = "https://github.com/Plonky3/Plonky3" }
p3-field = { git = "https://github.com/Plonky3/Plonky3" }

[profile.release]
lto = true
codegen-units = 1
```

### lib.rs

```rust
use p3_goldilocks::Goldilocks;
use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::Field;
use std::panic::catch_unwind;

/// NTT forward transform
///
/// # Safety
/// - `data` must point to valid array of `len` u64 values
/// - `len` must be power of 2
#[no_mangle]
pub unsafe extern "C" fn plonky3_ntt_forward(
    data: *mut u64,
    len: usize,
) -> i32 {
    // Wrap in catch_unwind to prevent Rust panics crossing FFI
    let result = catch_unwind(|| {
        let slice = std::slice::from_raw_parts_mut(data, len);

        // Convert u64 to Goldilocks
        let mut values: Vec<Goldilocks> = slice
            .iter()
            .map(|&x| Goldilocks::from_canonical_u64(x))
            .collect();

        // Perform NTT
        let dft = Radix2DitParallel::default();
        dft.dft_batch(&mut [values.as_mut_slice()]);

        // Convert back to u64
        for (i, v) in values.iter().enumerate() {
            slice[i] = v.as_canonical_u64();
        }
    });

    match result {
        Ok(_) => 0,   // Success
        Err(_) => -1, // Panic occurred
    }
}

/// Get Goldilocks prime for verification
#[no_mangle]
pub extern "C" fn plonky3_goldilocks_prime() -> u64 {
    // p = 2^64 - 2^32 + 1
    0xFFFFFFFF00000001u64
}

/// Check if value is in Montgomery form (for debugging)
#[no_mangle]
pub extern "C" fn plonky3_is_montgomery() -> i32 {
    // Test: create 1, check internal representation
    let one = Goldilocks::from_canonical_u64(1);
    let internal = one.as_canonical_u64();
    if internal == 1 { 0 } else { 1 }
}
```

### Tareas

| # | Tarea | Criterio de éxito |
|---|-------|-------------------|
| 2.1 | Crear estructura Cargo | `cargo new --lib plonky3_shim` |
| 2.2 | Agregar dependencias Plonky3 | `cargo build` compila |
| 2.3 | Implementar `plonky3_ntt_forward` | Función exportada |
| 2.4 | Implementar helpers de debug | `plonky3_is_montgomery` |
| 2.5 | Verificar símbolos exportados | `nm -D libplonky3_shim.so` |
| 2.6 | Test básico en C | Cargar .so y llamar función |

### Entregable

- `verification/plonky3/plonky3_shim/` compilable
- `libplonky3_shim.so` generado
- Test C que carga y ejecuta NTT

---

## Subfase 6A.3: Adaptadores de Orden

**Duración estimada**: 1 día
**Objetivo**: Detectar y adaptar diferencias de orden I/O entre Plonky3 y AMO-Lean.

### order_detector.c

```c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dlfcn.h>
#include "../generated/ntt_kernel.h"
#include "../generated/ntt_skeleton.c"

typedef int (*plonky3_ntt_fn)(uint64_t*, size_t);

typedef enum {
    ORDER_NN = 0,  // Natural-Natural
    ORDER_NR = 1,  // Natural-BitReverse
    ORDER_RN = 2,  // BitReverse-Natural
    ORDER_RR = 3,  // BitReverse-BitReverse
    ORDER_UNKNOWN = -1
} NTT_Order;

// AMO-Lean NTT with configurable order
static void amolean_ntt_order(uint64_t* data, size_t n, uint64_t omega,
                               int reverse_input, int reverse_output) {
    size_t log2_n = /* compute */;

    if (reverse_input) {
        bit_reverse_permute(data, n, log2_n);
    }

    ntt_forward(data, n, omega);  // Our verified implementation

    if (reverse_output) {
        bit_reverse_permute(data, n, log2_n);
    }
}

// Compare two arrays
static int arrays_equal(uint64_t* a, uint64_t* b, size_t n) {
    for (size_t i = 0; i < n; i++) {
        if (a[i] != b[i]) return 0;
    }
    return 1;
}

// Detect Plonky3's I/O order by testing all 4 combinations
NTT_Order detect_plonky3_order(plonky3_ntt_fn plonky3_ntt, size_t n, uint64_t omega) {
    uint64_t* input = malloc(n * sizeof(uint64_t));
    uint64_t* plonky3_result = malloc(n * sizeof(uint64_t));
    uint64_t* amolean_result = malloc(n * sizeof(uint64_t));

    // Initialize with known pattern
    for (size_t i = 0; i < n; i++) {
        input[i] = i + 1;
    }

    // Get Plonky3 result
    memcpy(plonky3_result, input, n * sizeof(uint64_t));
    plonky3_ntt(plonky3_result, n);

    // Test each order combination
    int orders[4][2] = {{0,0}, {0,1}, {1,0}, {1,1}};  // NN, NR, RN, RR

    for (int i = 0; i < 4; i++) {
        memcpy(amolean_result, input, n * sizeof(uint64_t));
        amolean_ntt_order(amolean_result, n, omega, orders[i][0], orders[i][1]);

        if (arrays_equal(plonky3_result, amolean_result, n)) {
            printf("Detected order: %s\n",
                   (char*[]){"NN", "NR", "RN", "RR"}[i]);
            free(input); free(plonky3_result); free(amolean_result);
            return (NTT_Order)i;
        }
    }

    printf("WARNING: No matching order found!\n");
    free(input); free(plonky3_result); free(amolean_result);
    return ORDER_UNKNOWN;
}
```

### Tareas

| # | Tarea | Criterio de éxito |
|---|-------|-------------------|
| 3.1 | Implementar `order_detector.c` | Compila y ejecuta |
| 3.2 | Probar con N=8, 16, 32 | Detecta orden consistentemente |
| 3.3 | Crear adaptador para AMO-Lean | `ntt_forward_adapted()` |
| 3.4 | Documentar orden detectado | En PLONKY3_ANALYSIS.md |

### Entregable

- `verification/plonky3/order_detector.c`
- Orden I/O de Plonky3 documentado
- Adaptador funcional

---

## Subfase 6A.4: Oracle Testing Suite

**Duración estimada**: 2 días
**Objetivo**: Verificar equivalencia semántica con vectores aleatorios.

### oracle_test.c

```c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <dlfcn.h>

#include "../generated/field_goldilocks.h"
#include "../generated/ntt_kernel.h"

// Test configuration
#define NUM_RANDOM_TESTS 100
#define MAX_DIFF_DISPLAY 5

typedef struct {
    size_t n;
    uint64_t omega;
    uint64_t n_inv;
} TestParams;

// Precomputed parameters (from Lean)
static const TestParams PARAMS[] = {
    {8,     0xFFFFFFFEFF000001ULL, 0xDFFFFFFF20000001ULL},
    {16,    /* from Lean */, /* from Lean */},
    {32,    /* ... */, /* ... */},
    {64,    /* ... */, /* ... */},
    {128,   /* ... */, /* ... */},
    {256,   0xBF79143CE60CA966ULL, 0xFEFFFFFF01000001ULL},
    {512,   /* ... */, /* ... */},
    {1024,  0x9D8F2AD78BFED972ULL, 0xFFBFFFFF00400001ULL},
};

// Random value in Goldilocks field
static uint64_t random_goldilocks(void) {
    uint64_t r = ((uint64_t)rand() << 32) | rand();
    return r % GOLDILOCKS_ORDER;
}

// Test result
typedef struct {
    int passed;
    int failed;
    int total;
} TestResult;

// Single test: compare Plonky3 vs AMO-Lean
static int test_single(plonky3_ntt_fn plonky3_ntt,
                        const TestParams* params,
                        uint64_t* input,
                        NTT_Order order) {
    size_t n = params->n;

    uint64_t* plonky3_result = malloc(n * sizeof(uint64_t));
    uint64_t* amolean_result = malloc(n * sizeof(uint64_t));

    memcpy(plonky3_result, input, n * sizeof(uint64_t));
    memcpy(amolean_result, input, n * sizeof(uint64_t));

    // Execute both
    plonky3_ntt(plonky3_result, n);
    ntt_forward_adapted(amolean_result, n, params->omega, order);

    // Compare
    int match = 1;
    for (size_t i = 0; i < n; i++) {
        if (plonky3_result[i] != amolean_result[i]) {
            match = 0;
            break;
        }
    }

    free(plonky3_result);
    free(amolean_result);
    return match;
}

// Test suite
TestResult run_oracle_tests(void* lib) {
    TestResult result = {0, 0, 0};

    plonky3_ntt_fn plonky3_ntt = dlsym(lib, "plonky3_ntt_forward");
    if (!plonky3_ntt) {
        fprintf(stderr, "Failed to load plonky3_ntt_forward\n");
        return result;
    }

    // Detect order once
    NTT_Order order = detect_plonky3_order(plonky3_ntt, 8, PARAMS[0].omega);

    for (size_t p = 0; p < sizeof(PARAMS)/sizeof(PARAMS[0]); p++) {
        const TestParams* params = &PARAMS[p];
        size_t n = params->n;

        printf("\nTesting N=%zu...\n", n);

        // Test 1: Sequential input [1, 2, 3, ..., n]
        uint64_t* seq_input = malloc(n * sizeof(uint64_t));
        for (size_t i = 0; i < n; i++) seq_input[i] = i + 1;

        if (test_single(plonky3_ntt, params, seq_input, order)) {
            printf("  Sequential input: PASS\n");
            result.passed++;
        } else {
            printf("  Sequential input: FAIL\n");
            result.failed++;
        }
        result.total++;
        free(seq_input);

        // Test 2: All zeros
        uint64_t* zero_input = calloc(n, sizeof(uint64_t));
        if (test_single(plonky3_ntt, params, zero_input, order)) {
            printf("  All zeros: PASS\n");
            result.passed++;
        } else {
            printf("  All zeros: FAIL\n");
            result.failed++;
        }
        result.total++;
        free(zero_input);

        // Test 3: All ones
        uint64_t* ones_input = malloc(n * sizeof(uint64_t));
        for (size_t i = 0; i < n; i++) ones_input[i] = 1;
        if (test_single(plonky3_ntt, params, ones_input, order)) {
            printf("  All ones: PASS\n");
            result.passed++;
        } else {
            printf("  All ones: FAIL\n");
            result.failed++;
        }
        result.total++;
        free(ones_input);

        // Test 4-N: Random inputs
        for (int r = 0; r < NUM_RANDOM_TESTS; r++) {
            uint64_t* rand_input = malloc(n * sizeof(uint64_t));
            for (size_t i = 0; i < n; i++) {
                rand_input[i] = random_goldilocks();
            }

            if (test_single(plonky3_ntt, params, rand_input, order)) {
                result.passed++;
            } else {
                result.failed++;
                if (result.failed <= MAX_DIFF_DISPLAY) {
                    printf("  Random test %d: FAIL\n", r);
                }
            }
            result.total++;
            free(rand_input);
        }

        printf("  Random tests: %d/%d passed\n",
               result.passed - 3, NUM_RANDOM_TESTS);
    }

    return result;
}

int main(void) {
    printf("═══════════════════════════════════════════════════════════\n");
    printf("  Plonky3 vs AMO-Lean Oracle Testing\n");
    printf("  Phase 6A: Verification Suite\n");
    printf("═══════════════════════════════════════════════════════════\n");

    srand(time(NULL));

    // Load Plonky3 shim
    void* lib = dlopen("./libplonky3_shim.so", RTLD_NOW);
    if (!lib) {
        fprintf(stderr, "Failed to load libplonky3_shim.so: %s\n", dlerror());
        return 1;
    }

    // Check Montgomery representation
    int (*is_montgomery)(void) = dlsym(lib, "plonky3_is_montgomery");
    if (is_montgomery && is_montgomery()) {
        printf("\nWARNING: Plonky3 uses Montgomery representation!\n");
        printf("         Need to convert values before comparison.\n\n");
    }

    // Run tests
    TestResult result = run_oracle_tests(lib);

    printf("\n═══════════════════════════════════════════════════════════\n");
    printf("  RESULTS: %d/%d tests passed (%.1f%%)\n",
           result.passed, result.total,
           100.0 * result.passed / result.total);
    printf("═══════════════════════════════════════════════════════════\n");

    dlclose(lib);

    return (result.failed == 0) ? 0 : 1;
}
```

### Tareas

| # | Tarea | Criterio de éxito |
|---|-------|-------------------|
| 4.1 | Implementar `oracle_test.c` | Compila |
| 4.2 | Obtener parámetros omega/n_inv de Lean | Para N=8 a N=1024 |
| 4.3 | Ejecutar tests N=8 | 100% pass |
| 4.4 | Ejecutar tests N=16,32,64 | 100% pass |
| 4.5 | Ejecutar tests N=128,256,512 | 100% pass |
| 4.6 | Ejecutar tests N=1024 | 100% pass |
| 4.7 | Documentar resultados | En PHASE6A_RESULTS.md |

### Criterio de Éxito

**100% de tests deben pasar.**

Si hay fallos:
1. Verificar orden I/O
2. Verificar Montgomery conversion
3. Verificar omega values
4. Debug con N=4 y comparar paso a paso

### Entregable

- `verification/plonky3/oracle_test.c`
- `verification/plonky3/oracle_test` ejecutable
- Log de ejecución con todos los tests passing

---

## Subfase 6A.5: Benchmark Comparativo

**Duración estimada**: 1 día
**Objetivo**: Medir performance relativa (no para competir, sino para entender).

### benchmark.c

```c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>
#include <dlfcn.h>

#include "../generated/field_goldilocks.h"
#include "../generated/ntt_kernel.h"

#define WARMUP_ITERATIONS 10
#define BENCHMARK_ITERATIONS 100

typedef struct {
    double plonky3_time_ms;
    double amolean_time_ms;
    double speedup;  // amolean_time / plonky3_time (>1 = Plonky3 faster)
} BenchmarkResult;

static double get_time_ms(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec * 1000.0 + tv.tv_usec / 1000.0;
}

BenchmarkResult benchmark_ntt(plonky3_ntt_fn plonky3_ntt,
                               size_t n, uint64_t omega) {
    BenchmarkResult result;

    uint64_t* data = malloc(n * sizeof(uint64_t));
    uint64_t* backup = malloc(n * sizeof(uint64_t));

    // Initialize
    for (size_t i = 0; i < n; i++) {
        data[i] = (i + 1) % GOLDILOCKS_ORDER;
        backup[i] = data[i];
    }

    // Warmup Plonky3
    for (int i = 0; i < WARMUP_ITERATIONS; i++) {
        memcpy(data, backup, n * sizeof(uint64_t));
        plonky3_ntt(data, n);
    }

    // Benchmark Plonky3
    double start = get_time_ms();
    for (int i = 0; i < BENCHMARK_ITERATIONS; i++) {
        memcpy(data, backup, n * sizeof(uint64_t));
        plonky3_ntt(data, n);
    }
    double end = get_time_ms();
    result.plonky3_time_ms = (end - start) / BENCHMARK_ITERATIONS;

    // Warmup AMO-Lean
    for (int i = 0; i < WARMUP_ITERATIONS; i++) {
        memcpy(data, backup, n * sizeof(uint64_t));
        ntt_forward(data, n, omega);
    }

    // Benchmark AMO-Lean
    start = get_time_ms();
    for (int i = 0; i < BENCHMARK_ITERATIONS; i++) {
        memcpy(data, backup, n * sizeof(uint64_t));
        ntt_forward(data, n, omega);
    }
    end = get_time_ms();
    result.amolean_time_ms = (end - start) / BENCHMARK_ITERATIONS;

    result.speedup = result.amolean_time_ms / result.plonky3_time_ms;

    free(data);
    free(backup);
    return result;
}

int main(void) {
    printf("═══════════════════════════════════════════════════════════\n");
    printf("  Plonky3 vs AMO-Lean Performance Benchmark\n");
    printf("  Phase 6A: Comparative Analysis\n");
    printf("═══════════════════════════════════════════════════════════\n\n");

    void* lib = dlopen("./libplonky3_shim.so", RTLD_NOW);
    if (!lib) {
        fprintf(stderr, "Failed to load shim: %s\n", dlerror());
        return 1;
    }

    plonky3_ntt_fn plonky3_ntt = dlsym(lib, "plonky3_ntt_forward");

    printf("| Size     | Plonky3 (ms) | AMO-Lean (ms) | Ratio      |\n");
    printf("|----------|--------------|---------------|------------|\n");

    size_t sizes[] = {256, 1024, 4096, 16384, 65536};
    uint64_t omegas[] = {/* from Lean for each size */};

    for (size_t i = 0; i < sizeof(sizes)/sizeof(sizes[0]); i++) {
        BenchmarkResult r = benchmark_ntt(plonky3_ntt, sizes[i], omegas[i]);

        const char* winner = r.speedup < 1.0 ? "AMO-Lean" : "Plonky3";
        printf("| N=%-6zu | %12.3f | %13.3f | %.2fx %-7s |\n",
               sizes[i], r.plonky3_time_ms, r.amolean_time_ms,
               r.speedup < 1.0 ? 1.0/r.speedup : r.speedup, winner);
    }

    printf("\n");
    printf("Note: AMO-Lean uses lazy reduction (Harvey 2014)\n");
    printf("Note: Plonky3 optimized for 31-bit fields, not 64-bit\n");

    dlclose(lib);
    return 0;
}
```

### Tareas

| # | Tarea | Criterio de éxito |
|---|-------|-------------------|
| 5.1 | Implementar `benchmark.c` | Compila |
| 5.2 | Ejecutar benchmarks N=256-65536 | Resultados obtenidos |
| 5.3 | Analizar diferencias | Documentar razones |
| 5.4 | Crear tabla comparativa | En PHASE6A_RESULTS.md |

### Interpretación Esperada

| Escenario | Significado |
|-----------|-------------|
| AMO-Lean más rápido | Nuestras optimizaciones funcionan mejor para Goldilocks |
| Plonky3 más rápido | Plonky3 tiene optimizaciones que podemos estudiar |
| Iguales (±10%) | Implementaciones equivalentes |

**No es una competencia.** El objetivo es entender diferencias, no "ganar".

### Entregable

- `verification/plonky3/benchmark.c`
- Tabla de resultados
- Análisis de diferencias

---

## Makefile Completo

```makefile
# verification/plonky3/Makefile

CC = gcc
CFLAGS = -O3 -Wall -Wextra -I../../generated
LDFLAGS = -ldl -lm

# Rust build
CARGO = cargo
RUST_TARGET = release

.PHONY: all clean shim test benchmark

all: shim order_detector oracle_test benchmark

# Build Rust shim
shim:
	cd plonky3_shim && $(CARGO) build --$(RUST_TARGET)
	cp plonky3_shim/target/$(RUST_TARGET)/libplonky3_shim.so . || \
	cp plonky3_shim/target/$(RUST_TARGET)/libplonky3_shim.dylib ./libplonky3_shim.so

# Build C programs
order_detector: order_detector.c shim
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS) -Wl,-rpath,'$$ORIGIN'

oracle_test: oracle_test.c shim
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS) -Wl,-rpath,'$$ORIGIN'

benchmark: benchmark.c shim
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS) -Wl,-rpath,'$$ORIGIN'

# Run tests
test: oracle_test
	./oracle_test

# Run benchmarks
bench: benchmark
	./benchmark

# Clean
clean:
	rm -f order_detector oracle_test benchmark libplonky3_shim.so
	cd plonky3_shim && $(CARGO) clean
```

---

## Riesgos y Mitigaciones Finales

| Riesgo | Probabilidad | Impacto | Mitigación |
|--------|--------------|---------|------------|
| Symbol clashes | Baja (cdylib) | Alto | Usar dlopen, no static link |
| Montgomery mismatch | Media | Alto | Detector en shim |
| Order mismatch | Alta | Alto | Auto-detector 4 variantes |
| Cargo/Make conflict | Baja | Medio | Makefile simple orquesta |
| macOS dylib naming | Media | Bajo | `cp .dylib .so` en Makefile |
| Plonky3 API changes | Baja | Medio | Pin versión en Cargo.toml |

---

## Criterios de Éxito Fase 6A

| Criterio | Requisito |
|----------|-----------|
| Oracle tests | **100% pass** para N ≤ 1024 |
| Documentación | PLONKY3_ANALYSIS.md completo |
| Build system | `make all` funciona en un comando |
| Reproducibilidad | Cualquiera puede clonar y ejecutar |

---

*Última actualización: 2026-01-29*
