# Consulta QA - Estrategia de Eliminación de Sorries

**Fecha**: 2026-01-30
**Fase**: Post-sesión 1 de eliminación de sorries
**Solicitante**: Claude (Programador)

---

## Contexto

Estamos intentando eliminar todos los sorries del proyecto amo-lean NTT (17 sorries + 7 axiomas = 24 items totales). Completamos la primera sesión con resultados mixtos.

### Resultados de Sesión 1:
- **S4 `ofStrict_bound`**: PROBADO (pero requirió agregar hipótesis)
- **S3 `lazy_sub_simulates`**: POSPUESTO (aritmética modular compleja)
- **S1 `ntt_coeff_add`**: NO INICIADO (requiere pruebas sobre foldl)
- **S2 `ntt_coeff_scale`**: NO INICIADO (similar a S1)

### Problemas Encontrados:

1. **Omega no maneja módulo**: El tactic `omega` falla con expresiones que contienen `%`

2. **GoldilocksField sin invariante tipado**: El tipo no enforce `value < ORDER`, solo lo mantiene como invariante implícito

3. **Tactics faltantes**: `ring_nf`, `push_neg`, `conv_lhs` no disponibles con imports actuales

4. **Complejidad subestimada**: Los sorries clasificados como "baja dificultad" requieren conocimiento profundo de Mathlib

---

## Preguntas Específicas

### 1. Priorización

Los sorries de Fase 1 (Fundamentos) están resultando más difíciles de lo esperado. ¿Deberíamos:

A) Persistir en Fase 1 hasta completarla
B) Saltar a sorries más simples en otras fases
C) Invertir tiempo en refactorización primero

### 2. Modificación de API

Para `ofStrict_bound`, agregamos una hipótesis `hx : x.value.toNat < ORDER.toNat`. Esto cambia la API del teorema.

¿Es esto aceptable, o deberíamos:
A) Refactorizar `GoldilocksField` para incluir el invariante en el tipo
B) Crear un tipo wrapper `ValidGoldilocksField` con el invariante
C) Usar un axioma en lugar de hipótesis

### 3. Aritmética Modular (S3)

El teorema `lazy_sub_simulates` requiere probar:
```
(a + 2p - b) % p = (a%p + p - b%p) % p
```

Donde `a, b < 2p`.

¿Conoces algún enfoque específico en Mathlib para este tipo de identidades modulares? ¿Hay algún lemma que maneje esto directamente?

### 4. Imports de Mathlib

¿Recomiendas agregar imports adicionales para tener acceso a:
- `ring` tactic
- `push_neg` tactic
- `Finset.sum` lemmas más avanzados

¿Hay riesgo de conflictos o aumento significativo en tiempo de compilación?

### 5. Estrategia General

Dado que el proyecto ya tiene 3 axiomas (de Radix4), ¿cuál es el balance aceptable entre:
- Tiempo invertido en pruebas formales complejas
- Uso de axiomas para propiedades matemáticamente válidas
- Refactorización de tipos para hacer pruebas más fáciles

---

## Archivos Relevantes

- `SORRY_ELIMINATION_PLAN.md`: Plan original con 24 items
- `SORRY_ELIMINATION_SESSION_1.md`: Progreso de esta sesión
- `AmoLean/NTT/Bounds.lean`: Contiene S3, S4
- `AmoLean/NTT/Spec.lean`: Contiene S1, S2
- `AmoLean/Field/Goldilocks.lean`: Tipo GoldilocksField

---

## Expectativa

Buscamos recomendaciones concretas sobre:
1. Siguiente paso inmediato
2. Cambios estructurales recomendados
3. Recursos o lemmas de Mathlib que investigar
