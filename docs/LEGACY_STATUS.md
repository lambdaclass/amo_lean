# AMO-Lean: Estado del Proyecto

**Fecha**: 2026-01-28
**Versión**: 2.0.0
**Build**: `lake build` compila exitosamente (723 módulos)
**Dirección**: Option A - Optimización Formal (ver [OPTION_A_ROADMAP.md](OPTION_A_ROADMAP.md))

---

## Resumen Ejecutivo

AMO-Lean es un **compilador de optimización formal** que transforma especificaciones matemáticas en código C optimizado con garantías de corrección.

### Objetivo Principal (Option A)

```
Spec Matemática (MatExpr)  →  E-Graph Saturation  →  Código C Optimizado
                               (reglas verificadas)   (correcto por construcción)
```

### Componentes Completados

1. **Motor de Reescritura Verificado** (0 `sorry`) - Core del optimizador
2. **E-Graph con Equality Saturation** - Encuentra optimizaciones
3. **Generación de Código C/SIMD** - Produce código ejecutable
4. **MatExpr + elemwise** - Soporta operaciones no-lineales

### Componentes de Referencia (Para Testing)

5. **Protocolo FRI** (Prover + Verifier) - Implementación de referencia
6. **Poseidon2/BN254** - Hash criptográfico de referencia

---

## Arquitectura

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           PIPELINE AMO-LEAN                                  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Nivel 6: Protocolo FRI                                                     │
│     ├── Prover/Verifier genérico [FRIField F] [CryptoHash F]               │
│     ├── TestField (XOR hash) - desarrollo rápido                           │
│     └── BN254 (Poseidon2) - producción criptográfica                       │
│                        ↓                                                    │
│  Nivel 5: Operaciones Vectoriales                                          │
│     ├── MatExpr (productos Kronecker, O(log N))                            │
│     ├── VecExpr (vectores con índice de longitud)                          │
│     └── Generación SIMD (intrinsics AVX2)                                  │
│                        ↓                                                    │
│  Nivel 4: Aritmética de Campo Finito                                       │
│     ├── Integración ZMod con Mathlib                                       │
│     └── Expresiones de potencia (constructor pow)                          │
│                        ↓                                                    │
│  Nivel 3: E-Graph + Equality Saturation                                    │
│     ├── Union-Find con compresión de caminos                               │
│     ├── E-matching con Pattern/Substitution                                │
│     └── Macro #compile_rules para teoremas Mathlib                         │
│                        ↓                                                    │
│  Nivel 2: Motor de Reescritura                                             │
│     ├── Tipo inductivo Expr α                                              │
│     ├── 12 reglas algebraicas (probadas correctas)                         │
│     └── Reescritura bottom-up hasta punto fijo                             │
│                        ↓                                                    │
│  Nivel 1: Generación de Código                                             │
│     └── exprToC, generateFriProtocol → código C                            │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Fases Completadas

| Fase | Descripción | Estado |
|------|-------------|--------|
| 1 | Modelo de juguete (Expr, reglas, motor) | ✅ Completado |
| 1.5 | Verificación completa (0 sorry) | ✅ Completado |
| 2 | E-Graph básico | ✅ Completado |
| 3 | Equality Saturation | ✅ Completado |
| 4 | Extensión de potencias | ✅ Completado |
| 5 | Operaciones vectoriales + SIMD | ✅ Completado |
| 6 | Protocolo FRI | ✅ Completado |
| 6.5 | Máquina de estados FRI | ✅ Completado |
| 6.6 | Differential fuzzing | ✅ Completado |
| **7** | **Integración Poseidon2** | **✅ Completado** |
| 7.1 | Especificación ejecutable | ✅ Completado |
| 7.2 | Extensión IR (elemwise) | ✅ Completado |
| 7.3 | CodeGen escalar + SIMD | ✅ Completado |
| 7.4 | Verificación vs referencia | ✅ Completado |
| 7.5 | Integración FRI + Migration | ✅ Completado |

---

## Estructura del Proyecto

```
amo-lean/
├── AmoLean.lean                    # Módulo principal
├── AmoLean/
│   ├── Basic.lean                  # AST, reglas, motor greedy
│   ├── Correctness.lean            # Pruebas de soundness (0 sorry)
│   ├── CodeGen.lean                # Generación de código C
│   ├── EGraph/                     # E-graph + saturation
│   ├── Vector/                     # VecExpr con longitud indexada
│   ├── Matrix/                     # MatExpr, productos Kronecker
│   ├── Sigma/                      # Sigma-SPL IR
│   ├── Verification/               # Semántica de referencia
│   ├── Protocols/Poseidon/         # Poseidon2 especificación + integración
│   │   ├── Spec.lean               # Permutación Poseidon2 pura
│   │   ├── Integration.lean        # Adaptadores para FRI
│   │   └── DomainSeparation.lean   # Tags de dominio
│   └── FRI/                        # Protocolo FRI genérico
│       ├── Fold.lean               # FRIField typeclass
│       ├── Hash.lean               # CryptoHash typeclass
│       ├── Merkle.lean             # Árboles Merkle genéricos
│       ├── Transcript.lean         # Fiat-Shamir transcript
│       ├── Prover.lean             # Generación de proofs
│       ├── Verifier.lean           # Verificación con errores estructurados
│       └── Fields/
│           ├── TestField.lean      # Campo de test (64-bit, XOR)
│           └── BN254.lean          # Campo BN254 con Poseidon2
├── Tests/
│   ├── E2EProverVerifier.lean      # Tests end-to-end
│   └── Phase3Audit.lean            # Auditoría de 4 dimensiones
├── Benchmarks/
│   └── NativeBenchmark.lean        # Benchmark compilado nativo
└── docs/
    ├── STATUS.md                   # Este archivo
    ├── ZKVM_ROADMAP.md             # Roadmap hacia zkVM
    └── poseidon/                   # Documentación Poseidon2
        ├── README.md               # Overview de la fase
        ├── PROGRESS.md             # Log detallado de progreso
        ├── ADR-001 a ADR-009       # Decisiones arquitectónicas
        └── migration/              # Documentación de migración
```

---

## Capacidades Actuales

### FRI Protocol

| Característica | Estado |
|----------------|--------|
| Commit phase (Merkle trees) | ✅ |
| Query phase (Merkle proofs) | ✅ |
| Fiat-Shamir transcript | ✅ |
| Verificación con errores estructurados | ✅ |
| Soporte multi-campo | ✅ |

### Campos Soportados

| Campo | Tamaño | Hash | Uso | Performance (degree 4096) |
|-------|--------|------|-----|---------------------------|
| TestField | 64-bit | XOR | Tests rápidos | ~300ms prove |
| BN254 | 254-bit | Poseidon2 | Producción | ~113s prove |

### Verificación

| Test | Resultado |
|------|-----------|
| E2E Prover/Verifier TestField | ✅ PASS |
| E2E Prover/Verifier BN254 | ✅ PASS |
| Soundness: commitment tampering | ✅ Detectado |
| Soundness: challenge tampering | ✅ Detectado |
| Soundness: query path corruption | ✅ Detectado |
| Soundness: wrong degree claim | ✅ Detectado |

---

## Decisiones de Diseño Clave

1. **Separación FRIField/CryptoHash**: Permite diferentes hashes para el mismo campo
2. **TestField para desarrollo**: XOR determinístico, 10-100x más rápido que Poseidon2
3. **VerifyError estructurado**: Errores con contexto (round, query, position, expected/actual)
4. **Diseño iterativo**: `Id.run do` con `for` loops, evita stack overflow

---

## Documentación Relacionada

| Documento | Propósito |
|-----------|-----------|
| [ZKVM_ROADMAP.md](ZKVM_ROADMAP.md) | Planificación hacia zkVM |
| [poseidon/README.md](poseidon/README.md) | Overview de integración Poseidon2 |
| [poseidon/PROGRESS.md](poseidon/PROGRESS.md) | Log detallado de implementación |
| [poseidon/ADR-*.md](poseidon/) | Decisiones arquitectónicas (9 ADRs) |
| [poseidon/migration/](poseidon/migration/) | Documentación de migración a campo genérico |

---

## Comandos Útiles

```bash
# Compilar todo
lake build

# Compilar tests
lake build Tests

# Ejecutar benchmark nativo
lake build fri-benchmark
./.lake/build/bin/fri-benchmark

# Ver tests E2E (en editor con Lean)
# Abrir Tests/E2EProverVerifier.lean y ejecutar #eval!
```

---

## Métricas del Proyecto

| Métrica | Valor |
|---------|-------|
| Líneas de código Lean | ~15,000 |
| Módulos | 723 |
| `sorry` en motor verificado | 0 |
| ADRs documentados | 9 |
| Tests E2E | 5 |
| Soundness tests | 4 |

---

*Última actualización: 2026-01-28*
