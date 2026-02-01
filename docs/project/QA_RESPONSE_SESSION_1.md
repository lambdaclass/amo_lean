# Respuesta QA - Sesión 1

**Fecha**: 2026-01-30
**Modelo QA**: Gemini 2.5 Pro (86.7% AIME 2025, mejor modelo para matemáticas)
**Veredicto**: Aprobar con Revisiones

---

## Resumen Ejecutivo

El QA identificó que el enfoque actual es sólido pero necesita ajustes tácticos antes de continuar. La recomendación principal es **detener la eliminación secuencial de sorries** y enfocarse en habilitar herramientas fundamentales primero.

---

## Prioridades Recomendadas

### Prioridad 0: Habilitar Tácticas Estándar (BLOQUEANTE)

**Acción inmediata**: Agregar `import Mathlib.Tactic` al proyecto.

```lean
import Mathlib.Tactic
```

Esto habilita:
- `ring` / `ring_nf` - Para identidades algebraicas
- `push_neg` - Para manipular negaciones
- `field_simp` - Para simplificar expresiones de campos
- `norm_num` - Para aritmética numérica
- `polyrith` (experimental) - Para relaciones polinomiales

**Riesgo**: Aumento moderado en tiempo de compilación.
**Beneficio**: Esencial para la mayoría de las pruebas algebraicas.

---

### Prioridad 1: Refactorizar GoldilocksField

**Problema actual**: El invariante `value < ORDER` es implícito (comentario, no tipo).

**Solución recomendada**: Usar tipo dependiente `Fin GOLDILOCKS_PRIME`.

```lean
-- Antes (problemático)
structure GoldilocksField where
  value : UInt64
  -- Invariant: value < ORDER (not enforced!)

-- Después (recomendado)
abbrev GoldilocksField := Fin GOLDILOCKS_PRIME
-- O equivalente:
structure GoldilocksField where
  value : UInt64
  h_valid : value.toNat < GOLDILOCKS_PRIME
```

**Impacto**:
- `ofStrict_bound` ya no necesitaría hipótesis extra
- Múltiples teoremas se simplifican
- Operaciones deben preservar el invariante

**Esfuerzo estimado**: 2-4 horas de refactorización

---

### Prioridad 2: Triage de Sorries Fáciles

Antes de atacar los sorries complejos (S1, S2, S3), identificar "low-hanging fruit":

- Sorries que son `native_decide` o `decide`
- Sorries que son `simp` directo
- Sorries que son `rfl` o `trivial`
- Bounds simples que `omega` puede resolver

**Objetivo**: Reducir el conteo de sorries rápidamente para momentum.

---

### Prioridad 3: Re-atacar S3 con ZMod p

**Insight clave del QA**: Usar `ZMod p` en lugar de aritmética modular sobre Nat.

```lean
import Mathlib.Data.ZMod.Basic

-- En ZMod p:
-- - 2*p y p son 0
-- - a % p es equivalente a (a : ZMod p)
-- - La prueba se vuelve trivial con ring
```

**Estrategia sugerida**:
1. Crear lema bridge: `∀ a : Nat, (a % p) = ((a : ZMod p) : Nat)`
2. Reescribir el goal a términos de ZMod
3. Probar con `ring` en ZMod (donde es trivial)
4. Transferir de vuelta a Nat

---

## Respuestas a Preguntas Específicas

### 1. Priorización
**Respuesta QA**: Detener Fase 1 secuencial. Primero habilitar tácticas (P0) y considerar refactorización (P1).

### 2. Modificación de API (ofStrict_bound con hipótesis)
**Respuesta QA**: Aceptable temporalmente, pero la solución correcta es refactorizar el tipo (P1). La hipótesis agregada es una "deuda técnica" que se propagará.

### 3. Aritmética Modular (S3)
**Respuesta QA**: Usar `ZMod p` de Mathlib. Es la abstracción correcta para aritmética modular. La prueba en ZMod es trivial con `ring`.

### 4. Imports de Mathlib
**Respuesta QA**: Sí, agregar `Mathlib.Tactic`. El riesgo de conflictos es bajo. El aumento en tiempo de compilación es aceptable dado el beneficio.

### 5. Balance Axiomas vs Pruebas
**Respuesta QA**: Target zero axiomas para un proyecto de verificación formal. Los 7 axiomas actuales son "deuda de verificación" que debería eliminarse. Cada axioma es un punto donde el compilador confía en el humano.

---

## Notas Adicionales del QA

1. **Sobre omega y %**: "omega no puede razonar sobre módulo porque % introduce relaciones no lineales. Esto es correcto y esperado."

2. **Sobre Nat vs ZMod**: "La aritmética modular en Nat es dolorosa porque Nat no tiene negativos. ZMod p es el tipo correcto para este dominio."

3. **Sobre el enfoque general**: "El proyecto tiene buena estructura. Los problemas encontrados son típicos de verificación formal - siempre hay más trabajo en las pruebas de lo esperado inicialmente."

---

## Plan de Acción Inmediato

1. [ ] Agregar `import Mathlib.Tactic` a archivos relevantes
2. [ ] Verificar que el proyecto compila
3. [ ] Probar `ring` en un caso simple
4. [ ] Evaluar impacto en tiempo de compilación
5. [ ] Decidir sobre refactorización de GoldilocksField

---

## Archivos a Modificar

- `AmoLean/NTT/Bounds.lean` - Agregar import Mathlib.Tactic
- `AmoLean/NTT/Spec.lean` - Agregar import Mathlib.Tactic
- `AmoLean/Field/Goldilocks.lean` - Potencial refactorización (P1)
