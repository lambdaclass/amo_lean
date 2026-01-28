# AMO-Lean: Roadmap Option A - Optimización Formal

**Fecha**: 2026-01-28
**Objetivo**: Compilador que transforma especificaciones matemáticas en código C optimizado verificado

---

## Visión

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           PIPELINE AMO-LEAN (Option A)                       │
│                                                                              │
│   Spec Matemática     →    E-Graph        →    Código C/SIMD                │
│   (MatExpr en Lean)        Saturation          Optimizado                   │
│                            (reglas                                          │
│                             verificadas)                                     │
│                                                                              │
│   Ejemplo:                                                                   │
│   poseidon_round =         [saturate +      →   void poseidon_avx2() {     │
│     MDS × sbox(s + rc)      extract]             __m256i v = ...            │
│                                                  }                           │
│                                                                              │
│   GARANTÍA: Código C ≡ Spec (por construcción)                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Estado Actual

### Componentes Existentes (Listos para Usar)

| Componente | Archivo | Estado |
|------------|---------|--------|
| E-Graph engine | `AmoLean/EGraph/` | ✅ Completo |
| Equality saturation | `AmoLean/EGraph/Saturate.lean` | ✅ Completo |
| Reglas algebraicas verificadas | `AmoLean/Basic.lean` | ✅ 12 reglas |
| MatExpr (matrices simbólicas) | `AmoLean/Matrix/Basic.lean` | ✅ Completo |
| VecExpr (vectores indexados) | `AmoLean/Vector/Basic.lean` | ✅ Completo |
| elemwise (operaciones no-lineales) | `AmoLean/Matrix/Basic.lean` | ✅ Completo |
| CodeGen C/AVX2 | `AmoLean/CodeGen.lean` | ✅ Completo |
| Sigma IR | `AmoLean/Sigma/Basic.lean` | ✅ Completo |

### Componentes de Referencia (Fuera del Pipeline, Útiles para Testing)

| Componente | Archivo | Uso |
|------------|---------|-----|
| Poseidon2 spec | `Protocols/Poseidon/Spec.lean` | Oráculo de referencia |
| FRI Prover | `FRI/Prover.lean` | Testing de código generado |
| FRI Verifier | `FRI/Verifier.lean` | Testing de código generado |
| BN254 field | `FRI/Fields/BN254.lean` | Aritmética de campo |

### Lo Que Falta (Trabajo Option A)

| Componente | Descripción | Esfuerzo |
|------------|-------------|----------|
| Poseidon2 como MatExpr | Expresar rounds como operaciones MatExpr | 1-2 semanas |
| FRI fold como MatExpr | Expresar folding como MatExpr | 1 semana |
| Pipeline spec→code | Conectar MatExpr → E-Graph → CodeGen | 1 semana |
| Reglas para Poseidon2 | Reglas de optimización específicas | 1-2 semanas |
| Validación diferencial | Comparar código generado vs spec | 1 semana |

---

## Fases de Implementación

### Fase 0: Proof of Concept (2 semanas)

**Objetivo**: Demostrar que el pipeline funciona end-to-end con un ejemplo simple.

**Entregable**: FRI fold expresado como MatExpr, optimizado, generando código C.

```lean
-- Input: FRI fold como MatExpr
def friFoldSpec (even odd : VecExpr F n) (α : F) : VecExpr F n :=
  VecExpr.add even (VecExpr.smul α odd)

-- Output: Código C generado
// void fri_fold(const uint64_t* even, const uint64_t* odd,
//               uint64_t alpha, uint64_t* out, size_t n) {
//     for (size_t i = 0; i < n; i++) {
//         out[i] = even[i] + alpha * odd[i];
//     }
// }
```

**Validación**:
- Código generado produce mismos resultados que `FRI/Prover.lean`
- Differential testing pasa

**Checklist Fase 0**:
- [ ] Expresar `friFold` como VecExpr/MatExpr
- [ ] Pasar por E-Graph (aunque no optimice mucho aún)
- [ ] Generar código C
- [ ] Validar contra implementación de referencia

---

### Fase 1: Poseidon2 como MatExpr (3-4 semanas)

**Objetivo**: Expresar Poseidon2 completo como operaciones MatExpr.

**Desafíos técnicos**:
1. S-box `x^5` → `elemwise (pow 5)` ✅ Ya existe
2. MDS matrix multiplication → `MatExpr.mul` ✅ Ya existe
3. Round constants addition → `MatExpr.add` ✅ Ya existe
4. Composición de rounds → Necesita definir

**Entregable**:

```lean
-- Poseidon2 full round como MatExpr
def poseidon2FullRound (state : MatExpr F 3 1) (rc : MatExpr F 3 1) : MatExpr F 3 1 :=
  MatExpr.mul MDS_external (MatExpr.elemwise (ElemOp.pow 5) (MatExpr.add state rc))

-- Poseidon2 partial round como MatExpr
def poseidon2PartialRound (state : MatExpr F 3 1) (rc : MatExpr F 3 1) : MatExpr F 3 1 :=
  let afterAdd := MatExpr.add state rc
  let afterSbox := MatExpr.updateFirst (elemwise (ElemOp.pow 5)) afterAdd  -- Solo primer elemento
  MatExpr.mul MDS_internal afterSbox
```

**Validación**:
- Comparar output de código generado vs `Spec.lean`
- Usar test vectors del paper Poseidon2

**Checklist Fase 1**:
- [ ] Definir MDS matrices como MatExpr constantes
- [ ] Definir round constants como MatExpr constantes
- [ ] Expresar full round como MatExpr
- [ ] Expresar partial round como MatExpr (requiere `updateFirst` o similar)
- [ ] Componer 64 rounds en expresión completa
- [ ] Pasar por E-Graph
- [ ] Generar código C
- [ ] Validar contra `Spec.lean` (differential testing)

---

### Fase 2: Reglas de Optimización (2-3 semanas)

**Objetivo**: Añadir reglas al E-Graph que optimicen Poseidon2 y FRI.

**Reglas potenciales**:

```lean
-- Fusión de MDS × (state + rc) cuando rc es constante
theorem mds_add_fusion : MDS × (s + rc) = MDS × s + MDS × rc

-- Square chain para x^5: x^5 = x * (x^2)^2 (3 muls en lugar de 4)
theorem pow5_square_chain : x^5 = x * (x * x) * (x * x)

-- Fusión de loops cuando hay operaciones independientes
theorem loop_fusion : map f (map g xs) = map (f ∘ g) xs
```

**Entregable**: Código generado es más eficiente que traducción directa.

**Checklist Fase 2**:
- [ ] Identificar patrones de optimización en Poseidon2
- [ ] Expresar como reglas de reescritura
- [ ] Probar corrección de cada regla en Lean
- [ ] Añadir reglas al E-Graph
- [ ] Medir speedup del código generado
- [ ] Documentar cada optimización

---

### Fase 3: CodeGen Avanzado (3-4 semanas)

**Objetivo**: Generar código SIMD de alta calidad.

**Entregables**:
1. **AVX2 para Poseidon2**: Vectorizar state de 3 elementos
2. **Loop unrolling**: Desenrollar rounds cuando es beneficioso
3. **Register allocation**: Minimizar spills a memoria

**Checklist Fase 3**:
- [ ] Analizar código generado actual (assembly)
- [ ] Identificar cuellos de botella
- [ ] Implementar estrategias de vectorización
- [ ] Benchmark contra implementaciones de referencia (HorizenLabs/poseidon2)
- [ ] Documentar decisiones de CodeGen

---

### Fase 4: Integración y API (2-3 semanas)

**Objetivo**: API limpia para usuarios de AMO-Lean.

**Entregables**:

```lean
-- API de alto nivel
def compileToC (spec : MatExpr F m n) (config : CompileConfig) : IO String := do
  let optimized ← optimize spec config.rules
  let code ← generateC optimized config.target
  return code

-- Ejemplo de uso
#eval compileToC poseidon2Permutation {
  target := .avx2,
  unrollFactor := 4
}
```

**Checklist Fase 4**:
- [ ] Definir `CompileConfig` con opciones
- [ ] API `compileToC` limpia
- [ ] Documentación de uso
- [ ] Ejemplos completos
- [ ] Tests de integración

---

## Prioridades Adaptadas a Option A

### Prioridad #1: Pipeline Funcional (Fases 0-1)

**Meta**: Demostrar que MatExpr → E-Graph → C funciona con Poseidon2.

**Resultado**: Código C que computa Poseidon2, generado automáticamente, verificado correcto.

### Prioridad #2: Optimización Real (Fases 2-3)

**Meta**: Código generado competitivo con implementaciones manuales.

**Resultado**: Performance dentro de 2x de HorizenLabs/poseidon2 (Rust optimizado a mano).

### Prioridad #3: Más Campos (Paralelo a Fases 1-3)

**Meta**: Soportar Goldilocks además de BN254.

**Trabajo**:
- Parametrizar MatExpr sobre el campo
- Cargar parámetros Poseidon2 para Goldilocks
- Validar con test vectors

### Prioridad #4: Verificación Formal Completa (Post Fase 4)

**Meta**: Pruebas en Lean de que código generado ≡ spec.

**Trabajo**:
- Formalizar semántica de C subset
- Probar corrección de CodeGen
- Probar corrección de cada regla de optimización

---

## Timeline Estimado

| Fase | Duración | Acumulado |
|------|----------|-----------|
| Fase 0: PoC | 2 semanas | 2 semanas |
| Fase 1: Poseidon2 MatExpr | 3-4 semanas | 6 semanas |
| Fase 2: Reglas optimización | 2-3 semanas | 9 semanas |
| Fase 3: CodeGen avanzado | 3-4 semanas | 13 semanas |
| Fase 4: API | 2-3 semanas | 16 semanas |

**Total: ~4 meses** para pipeline completo y optimizado.

---

## Uso del Trabajo Existente (FRI+Poseidon2)

El trabajo de los últimos días NO se pierde:

| Componente | Uso en Option A |
|------------|-----------------|
| `Spec.lean` | **Oráculo de referencia** - validar código generado |
| `Prover.lean` | **Testing** - comparar proofs generados por código C |
| `Verifier.lean` | **Testing** - verificar que proofs de código C son válidos |
| `BN254.lean` | **Aritmética** - reusar para evaluación de MatExpr |
| Tests E2E | **Regression** - asegurar que refactoring no rompe nada |

---

## Resultado Final

Al completar Option A tendrás:

**Un compilador que:**
- Toma: Especificación matemática (MatExpr)
- Produce: Código C/AVX2 optimizado
- Garantiza: Corrección por construcción

**Que puedes usar para:**
1. Generar primitivos criptográficos para zkVM
2. Explorar optimizaciones sin riesgo de bugs
3. Tener código auditado (la spec es la documentación)

---

*Creado: 2026-01-28*
