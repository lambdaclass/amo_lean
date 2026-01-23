# AMO-Lean: Estado del Proyecto y Roadmap

## Estado Actual del Proyecto

### ¿Qué puede hacer?

```
┌─────────────────────────────────────────────────────────────────┐
│                    Pipeline AMO-Lean                            │
│                                                                 │
│  Expr α ──→ Rewrite Engine ──→ Simplified Expr ──→ C Code      │
│                                                                 │
│  x*(y+0)*1  ──→  algebraicRules  ──→  x*y  ──→  int64_t f() {  │
│                                                   return x*y;   │
│                                                 }               │
└─────────────────────────────────────────────────────────────────┘
```

**Capacidades concretas:**
1. **AST de expresiones** (`Expr α`): constantes, variables, suma, multiplicación
2. **Semántica denotacional**: `denote` conecta sintaxis con semántica de Mathlib
3. **8 reglas de reescritura verificadas**: identidades (+0, *1), aniquiladores (*0), distributividad
4. **Motor de reescritura bottom-up** con iteración a punto fijo
5. **Generación de código C** con let-lifting (forma SSA)
6. **Integración con Mathlib** para tipos algebraicos (Semiring, Ring)

### Estructura de Archivos

```
AmoLean/
├── Basic.lean              # AST, semántica, reglas, motor de reescritura
├── Correctness.lean        # Pruebas de soundness para reglas
├── MathlibIntegration.lean # Conexión con estructuras algebraicas de Mathlib
├── CodeGen.lean            # Generación de código C
└── AmoLean.lean            # Módulo principal y ejemplos
```

---

## Historial de Problemas y Soluciones

| Problema | Causa | Solución |
|----------|-------|----------|
| Lean 4.3.0 incompatible | Mathlib requiere versiones recientes | Actualización a 4.16.0 |
| `leanOptions` no existe | API de Lake cambió | Nueva sintaxis de lakefile |
| `BEq` vs `Eq` en pruebas | Las reglas usan `==` pero pruebas necesitan `=` | `LawfulBEq` + lemas `beq_zero_eq`/`beq_one_eq` |
| `partial` impide inducción | Lean no genera principio de inducción para `partial` | Documentado; requiere rediseño con `WellFounded` |
| `Inhabited` faltante | `partial def` requiere tipo habitado | `deriving Inhabited` |
| Bitwise no disponible | `Int.land` no está en el prelude | Comentar `rule_mul_pow2` |

### Deuda Técnica Principal

El problema más significativo es estructural: `rewriteBottomUp` está definido como `partial`, lo que impide probar su corrección por inducción. Esto requiere:

```lean
-- Actual (no permite inducción):
partial def rewriteBottomUp (rules) : Expr α → Expr α

-- Necesario (permite inducción):
def rewriteBottomUp (rules) : Expr α → Expr α :=
  fun e => e.recOn ...  -- usando el eliminador de Expr
  termination_by e => sizeOf e
```

---

## Relación Toy Model ↔ Optimizador FRI Completo

### Arquitectura por Niveles

```
┌────────────────────────────────────────────────────────────────────────┐
│                         NIVELES DE ABSTRACCIÓN                         │
├────────────────────────────────────────────────────────────────────────┤
│                                                                        │
│  Nivel 4: Protocolo FRI Completo                                       │
│           ├── Compromisos Merkle                                       │
│           ├── Rondas de plegado (folding)                              │
│           └── Verificación de proximidad                               │
│                           ↑                                            │
│  Nivel 3: Operaciones sobre Polinomios                                 │
│           ├── FFT/NTT verificada                                       │
│           ├── Interpolación                                            │
│           └── Evaluación multi-punto                                   │
│                           ↑                                            │
│  Nivel 2: Aritmética de Campo Finito                                   │
│           ├── F_p (campo primo)                                        │
│           ├── Extensiones de campo                                     │
│           └── Operaciones Montgomery/Barrett                           │
│                           ↑                                            │
│  Nivel 1: Expresiones Aritméticas  ◄──── ESTAMOS AQUÍ (Toy Model)     │
│           ├── AST genérico                                             │
│           ├── Reglas de reescritura                                    │
│           └── Generación de código                                     │
│                                                                        │
└────────────────────────────────────────────────────────────────────────┘
```

### Extensiones Necesarias para FRI

El toy model maneja `Expr α` donde `α` es un Semiring genérico. Para FRI necesitamos:

```lean
-- Toy Model actual:
inductive Expr (α : Type) where
  | const : α → Expr α
  | var : VarId → Expr α
  | add : Expr α → Expr α → Expr α
  | mul : Expr α → Expr α → Expr α

-- Para FRI necesitaríamos:
inductive FRIExpr where
  | fieldElem : ZMod p → FRIExpr           -- Elementos de campo
  | poly : Polynomial (ZMod p) → FRIExpr    -- Polinomios
  | fft : FRIExpr → FRIExpr                 -- Transformada
  | fold : FRIExpr → FRIExpr → FRIExpr      -- Operación de plegado FRI
  | merkleRoot : FRIExpr → FRIExpr          -- Compromiso
  | queryAt : FRIExpr → Nat → FRIExpr       -- Evaluación en punto
```

---

## Roadmap hacia Producción

### Fase 1: Completar el Toy Model (ACTUAL)

- [ ] Redefinir `rewriteBottomUp` con terminación demostrable
- [ ] Probar `rewriteBottomUp_sound` y `simplify_sound`
- [ ] Implementar E-graph básico para exploración de equivalencias
- [ ] Agregar más reglas (asociatividad, conmutatividad)
- [ ] Tests de corrección end-to-end

### Fase 2: Aritmética de Campo Finito

- [ ] Integrar `ZMod p` de Mathlib
- [ ] Implementar/verificar aritmética Montgomery
- [ ] Optimizaciones específicas: reducción de Barrett, Karatsuba
- [ ] Reglas de reescritura para campos finitos

**Referencia clave:** [Fiat-Crypto](https://github.com/mit-plv/fiat-crypto)

### Fase 3: Polinomios y FFT

- [ ] Representación de polinomios (coeficientes vs evaluaciones)
- [ ] FFT/NTT con prueba de corrección
- [ ] Conversiones verificadas entre representaciones
- [ ] Optimizaciones: Cooley-Tukey, Good-Thomas

### Fase 4: Protocolo FRI

- [ ] Estructura de datos para rondas FRI
- [ ] Operación de plegado verificada
- [ ] Generación de queries
- [ ] Merkle trees verificados
- [ ] Prueba de soundness del protocolo

**Referencias:**
- [FRI original](https://eccc.weizmann.ac.il/report/2017/134/) - Ben-Sasson et al.
- [DEEP-FRI](https://eprint.iacr.org/2019/336) - optimizaciones
- [ethSTARK](https://eprint.iacr.org/2021/582) - implementación práctica

### Fase 5: Generación de Código Verificada

- [ ] Backend para múltiples targets (C, Rust, assembly)
- [ ] Pruebas de preservación semántica en code generation
- [ ] Optimizaciones de bajo nivel (vectorización, paralelismo)
- [ ] Integración con compiladores verificados

**Referencias:**
- [Bedrock2](https://github.com/mit-plv/bedrock2)
- [CakeML](https://cakeml.org/)
- [CompCert](https://compcert.org/)

### Fase 6: Integración y Producción

- [ ] API estable para usuarios
- [ ] Benchmarks contra implementaciones no verificadas
- [ ] Documentación completa
- [ ] Integración con sistemas de prueba existentes (Plonky2, etc.)
- [ ] Auditoría de seguridad

---

## Referencias Bibliográficas

### E-graphs y Equality Saturation
- **egg: Fast and Extensible Equality Saturation** - Willsey et al. 2021
- **Rewrite Rule Inference Using Equality Saturation** - Nandi et al.
- **egglog** - E-graphs + Datalog

### Verificación de Criptografía
- **Fiat-Crypto: Synthesizing Correct-by-Construction Code** - Erbsen et al.
- **Simple High-Level Code For Cryptographic Arithmetic** - continuación

### Optimización Verificada
- **Verifying and Synthesizing Constant-Resource Implementations**
- **Alive2: Bounded Translation Validation for LLVM**

### FRI y STARKs
- **Proximity Gaps for Reed-Solomon Codes** - análisis teórico
- **STARK paper original** - Ben-Sasson et al. 2018

---

## Estimación de Complejidad

```
                        Complejidad    Dependencias
                        ───────────    ────────────
Toy Model Completo      ████░░░░░░     Ninguna
E-graph Básico          █████░░░░░     Toy Model
Campo Finito            ██████░░░░     Mathlib ZMod
FFT Verificada          ███████░░░     Campo Finito
FRI Completo            █████████░     Todo lo anterior
Producción              ██████████     FRI + Ingeniería
```

---

*Documento generado: Enero 2026*
*Última actualización: Estado post-pruebas de soundness*
