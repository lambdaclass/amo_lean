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
4. **Motor de reescritura bottom-up** con iteración a punto fijo - **COMPLETAMENTE VERIFICADO**
5. **Generación de código C** con let-lifting (forma SSA)
6. **Integración con Mathlib** para tipos algebraicos (Semiring, Ring)
7. **0 `sorry`** en todo el proyecto - todas las pruebas de corrección están completas

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
| `partial` impide inducción | Lean no genera principio de inducción para `partial` | **RESUELTO**: Recursión estructural + `termination_by` |
| `Inhabited` faltante | `partial def` requiere tipo habitado | `deriving Inhabited` |
| Bitwise no disponible | `Int.land` no está en el prelude | Comentar `rule_mul_pow2` |
| 2 `sorry` en Correctness.lean | Dependían de `partial` | **RESUELTO**: Pruebas completas por inducción |

### Deuda Técnica Principal - RESUELTA (Enero 2026)

~~El problema más significativo era estructural: `rewriteBottomUp` estaba definido como `partial`.~~

**SOLUCIÓN IMPLEMENTADA:**

```lean
-- Antes (no permitía inducción):
partial def rewriteBottomUp (rules) : Expr α → Expr α

-- Ahora (permite inducción estructural):
def rewriteBottomUp (rules : List (RewriteRule α)) : Expr α → Expr α
  | const c => rewriteAtRoot rules (const c)
  | var v => rewriteAtRoot rules (var v)
  | add e1 e2 => rewriteAtRoot rules (add (rewriteBottomUp rules e1) (rewriteBottomUp rules e2))
  | mul e1 e2 => rewriteAtRoot rules (mul (rewriteBottomUp rules e1) (rewriteBottomUp rules e2))
termination_by e => sizeOf e
```

**Cambios realizados:**
1. `rewriteBottomUp`: Recursión estructural con `termination_by e => sizeOf e`
2. `rewriteToFixpoint`: Pattern matching sobre `Nat` para terminación obvia
3. `lowerExpr` (CodeGen): Mismo patrón de recursión estructural

**Pruebas completadas:**
- `rewriteBottomUp_sound`: Por inducción sobre `Expr α`
- `rewriteToFixpoint_sound`: Por inducción sobre `fuel : Nat`
- `simplify_sound`: Composición de los lemas anteriores
- `algebraicRules_sound`: Lema auxiliar para las 6 reglas base

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

### Fase 1: Toy Model ✅ COMPLETADA

- [x] AST `Expr α` inductivo
- [x] Semántica denotacional
- [x] 8 reglas de reescritura
- [x] Motor bottom-up + punto fijo
- [x] Generación de código C

### Fase 1.5: Verificación Completa ✅ COMPLETADA (Enero 2026)

- [x] Redefinir `rewriteBottomUp` sin `partial` (recursión estructural)
- [x] Redefinir `rewriteToFixpoint` sin `partial` (pattern matching)
- [x] Probar `rewriteBottomUp_sound` por inducción
- [x] Probar `rewriteToFixpoint_sound` por inducción
- [x] Probar `simplify_sound`
- [x] 0 `sorry` en el proyecto

### Fase 2: E-graph y Equality Saturation (PRÓXIMA)

- [ ] Estructuras: `EClassId`, `ENode`, `EClass`, `EGraph`
- [ ] Union-find + hashcons
- [ ] Operaciones: `add`, `merge`, `find`, `rebuild`
- [ ] E-matching simple
- [ ] Saturación con las 8 reglas existentes
- [ ] Extracción con cost model

**Justificación:** La reescritura greedy actual pierde oportunidades de optimización.
E-graphs permiten explorar múltiples formas equivalentes simultáneamente.

### Fase 3: Mathlib Extendida sobre E-graph

- [ ] Macro `#compile_rules` para extracción automática
- [ ] Reglas de conmutatividad y asociatividad
- [ ] E-class analysis para síntesis de instancias

### Fase 4: Aritmética de Campo Finito

- [ ] Integrar `ZMod p` de Mathlib
- [ ] Implementar/verificar aritmética Montgomery
- [ ] Optimizaciones específicas: reducción de Barrett, Karatsuba
- [ ] Reglas de reescritura para campos finitos

**Referencia clave:** [Fiat-Crypto](https://github.com/mit-plv/fiat-crypto)

### Fase 5: Polinomios y FFT

- [ ] Representación de polinomios (coeficientes vs evaluaciones)
- [ ] FFT/NTT con prueba de corrección
- [ ] Conversiones verificadas entre representaciones
- [ ] Optimizaciones: Cooley-Tukey, Good-Thomas

### Fase 6: Protocolo FRI

- [ ] Estructura de datos para rondas FRI
- [ ] Operación de plegado verificada
- [ ] Generación de queries
- [ ] Merkle trees verificados
- [ ] Prueba de soundness del protocolo

**Referencias:**
- [FRI original](https://eccc.weizmann.ac.il/report/2017/134/) - Ben-Sasson et al.
- [DEEP-FRI](https://eprint.iacr.org/2019/336) - optimizaciones
- [ethSTARK](https://eprint.iacr.org/2021/582) - implementación práctica

### Fase 7: Generación de Código Verificada

- [ ] Backend para múltiples targets (C, Rust, assembly)
- [ ] Pruebas de preservación semántica en code generation
- [ ] Optimizaciones de bajo nivel (vectorización, paralelismo)
- [ ] Integración con compiladores verificados

**Referencias:**
- [Bedrock2](https://github.com/mit-plv/bedrock2)
- [CakeML](https://cakeml.org/)
- [CompCert](https://compcert.org/)

### Fase 8: Integración y Producción

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
                        Complejidad    Estado           Dependencias
                        ───────────    ──────           ────────────
Fase 1: Toy Model       ████░░░░░░     ✅ COMPLETADA    Ninguna
Fase 1.5: Verificación  ████░░░░░░     ✅ COMPLETADA    Toy Model
Fase 2: E-graph         █████░░░░░     ⏳ PRÓXIMA       Verificación
Fase 3: Mathlib Ext     █████░░░░░     🔜 Planificada   E-graph
Fase 4: Campo Finito    ██████░░░░     🔜 Planificada   Mathlib ZMod
Fase 5: FFT             ███████░░░     🔜 Planificada   Campo Finito
Fase 6: FRI             █████████░     🔜 Planificada   Todo lo anterior
Fase 7: CodeGen         ██████████     🔜 Planificada   FRI
Fase 8: Producción      ██████████     🔜 Planificada   Todo + Ingeniería
```

---

*Documento generado: Enero 2026*
*Última actualización: 23 Enero 2026 - Fase 1.5 completada (0 sorry)*

*Documento generado: Enero 2026*
*Última actualización: Estado post-pruebas de soundness*
