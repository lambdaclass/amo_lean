# AMO-Lean: Estado del Proyecto

*Documento generado: 23 de Enero 2026*

---

## 1. Estado Actual del Proyecto

### Pipeline Funcional

```
Expr α ──→ Motor de Reescritura ──→ Expr Simplificado ──→ Código C

Ejemplo: x*(y+0)*1  ──→  x*y  ──→  int64_t f() { return x*y; }
```

### Capacidades Implementadas

| Componente | Estado | Archivo |
|------------|--------|---------|
| AST de expresiones (`Expr α`) | ✅ Completo | `Basic.lean` |
| Semántica denotacional (`denote`) | ✅ Completo | `Basic.lean` |
| 8 reglas de reescritura | ✅ Implementadas | `Basic.lean` |
| Pruebas de soundness (reglas individuales) | ✅ 8/8 probadas | `Correctness.lean` |
| Motor bottom-up + punto fijo | ✅ Verificado | `Basic.lean` |
| Prueba del motor completo | ✅ **COMPLETADA** | `Correctness.lean` |
| Generación de código C (SSA) | ✅ Funciona | `CodeGen.lean` |
| Integración Mathlib | ✅ Básica | `MathlibIntegration.lean` |
| **`sorry` en el proyecto** | ✅ **0** | Todas las pruebas completas |

### Reglas de Reescritura Implementadas

- `x + 0 → x`, `0 + x → x` (identidades aditivas)
- `x * 1 → x`, `1 * x → x` (identidades multiplicativas)
- `x * 0 → 0`, `0 * x → 0` (aniquiladores)
- `a * (b + c) → a*b + a*c` (distributividad izquierda)
- `(a + b) * c → a*c + b*c` (distributividad derecha)

---

## 2. Historial de Problemas y Soluciones

### Problemas Resueltos

| Commit | Problema | Solución |
|--------|----------|----------|
| `88377dd` | Lean 4.3.0 incompatible con Mathlib | Upgrade a Lean 4.16.0 |
| `88377dd` | API de Lake cambió (`leanOptions` no existe) | Nueva sintaxis de lakefile |
| `1b278de` | Reglas usan `==` (BEq) pero pruebas necesitan `=` | Lemas `beq_zero_eq`/`beq_one_eq` + `LawfulBEq` |
| `88377dd` | `partial def` requiere tipo habitado | `deriving Inhabited` |
| `ef24802` | Operaciones bitwise no disponibles | Comentar `rule_mul_pow2` |

### Deuda Técnica Principal - ✅ RESUELTA (Enero 2026)

~~El problema estructural más importante era `rewriteBottomUp` definido como `partial`.~~

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

**Pruebas completadas:**
- `rewriteBottomUp_sound`: Por inducción sobre `Expr α`
- `rewriteToFixpoint_sound`: Por inducción sobre `fuel : Nat`
- `simplify_sound`: Composición de los lemas anteriores

---

## 3. Relación Toy Model ↔ Optimizador FRI Completo

### Arquitectura por Niveles

```
┌────────────────────────────────────────────────────────────────┐
│  Nivel 4: Protocolo FRI                                        │
│           └── Merkle, folding, verificación de proximidad      │
│                           ↑                                    │
│  Nivel 3: Polinomios                                           │
│           └── FFT/NTT, interpolación, evaluación               │
│                           ↑                                    │
│  Nivel 2: Aritmética de Campo Finito                           │
│           └── F_p, extensiones, Montgomery/Barrett             │
│                           ↑                                    │
│  Nivel 1: Expresiones Aritméticas  ◄── TOY MODEL (AQUÍ)       │
│           └── AST, reglas, reescritura, codegen                │
└────────────────────────────────────────────────────────────────┘
```

### El Rol del Toy Model

El toy model establece la **infraestructura base**:
- Cómo representar expresiones
- Cómo aplicar reglas de reescritura
- Cómo probar que las transformaciones son correctas
- Cómo generar código

### Extensión Necesaria para FRI

```lean
-- Toy model actual:
inductive Expr (α : Type) where
  | const | var | add | mul

-- Para FRI necesitarías:
inductive FRIExpr where
  | fieldElem : ZMod p → FRIExpr        -- elementos de campo
  | poly : Polynomial (ZMod p) → FRIExpr -- polinomios
  | fft : FRIExpr → FRIExpr              -- transformada
  | fold : FRIExpr → FRIExpr → FRIExpr   -- plegado FRI
  | merkleRoot : FRIExpr → FRIExpr       -- compromiso
```

---

## 4. Roadmap hacia Producción

### Fase 1: Toy Model ✅ COMPLETADA
- [x] AST `Expr α` inductivo
- [x] Semántica denotacional
- [x] 8 reglas de reescritura
- [x] Motor bottom-up + punto fijo
- [x] Generación de código C

### Fase 1.5: Verificación Completa ✅ COMPLETADA (Enero 2026)
- [x] Redefinir `rewriteBottomUp` sin `partial`
- [x] Redefinir `rewriteToFixpoint` sin `partial`
- [x] Probar `rewriteBottomUp_sound`
- [x] Probar `rewriteToFixpoint_sound`
- [x] Probar `simplify_sound`
- [x] 0 `sorry` en el proyecto

### Fase 2: E-graph y Equality Saturation (PRÓXIMA)
- [ ] Estructuras: `EClassId`, `ENode`, `EClass`, `EGraph`
- [ ] Union-find + hashcons
- [ ] E-matching simple
- [ ] Saturación con las 8 reglas existentes
- [ ] Extracción con cost model

### Fase 3: Mathlib Extendida sobre E-graph
- [ ] Macro `#compile_rules`
- [ ] Reglas de conmutatividad y asociatividad
- [ ] E-class analysis

### Fase 4: Aritmética de Campo Finito
- [ ] Integrar `ZMod p` de Mathlib
- [ ] Aritmética Montgomery/Barrett verificada
- [ ] Reglas específicas para campos finitos

### Fase 5: Polinomios y FFT
- [ ] Representación de polinomios (coeficientes ↔ evaluaciones)
- [ ] FFT/NTT verificada
- [ ] Optimizaciones: Cooley-Tukey

### Fase 6: Protocolo FRI
- [ ] Estructura de rondas FRI
- [ ] Operación de folding verificada
- [ ] Merkle trees
- [ ] Prueba de soundness del protocolo

### Fase 7: Generación de Código Verificada
- [ ] Backends múltiples (C, Rust, assembly)
- [ ] Pruebas de preservación semántica end-to-end
- [ ] Vectorización automática

### Fase 8: Producción
- [ ] API estable
- [ ] Benchmarks vs implementaciones no verificadas
- [ ] Auditoría de seguridad

---

## 5. Referencias Bibliográficas

### E-graphs y Equality Saturation
- **egg: Fast and Extensible Equality Saturation** (Willsey et al. POPL 2021)
- **egglog** - combinación de E-graphs con Datalog

### Verificación de Criptografía
- **Fiat-Crypto** (MIT) - referencia principal
- **Hacspec** - especificación ejecutable de criptografía

### Para FFT Verificada
- **Verified Textbook Algorithms** - demostraciones en Lean/Coq

### Para FRI
- **FRI paper original** - Ben-Sasson et al. 2017
- **DEEP-FRI** - optimizaciones (2019)
- **ethSTARK documentation** - implementación práctica
- **Proximity Gaps for Reed-Solomon Codes** - análisis teórico

### Para Code Generation
- **Bedrock2** (MIT) - generación verificada
- **CakeML** - compilador verificado
- **CompCert** - compilador C verificado

### Implementaciones de Referencia
- **Plonky2** (Polygon)
- **Stone prover** (StarkWare)
- **Winterfell** (Rust)

---

## 6. Estimación de Complejidad

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

*Documento generado: 23 de Enero 2026*
*Última actualización: 23 Enero 2026 - Fase 1.5 completada (0 sorry)*
