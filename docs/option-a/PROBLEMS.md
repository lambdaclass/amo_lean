# Option A: Problemas Encontrados y Soluciones

Este documento registra todos los problemas encontrados durante Option A y sus soluciones.

---

## Formato de Entrada

```
## P-XXX: Título del Problema

**Fecha**: YYYY-MM-DD
**Fase**: N
**Severidad**: Crítica / Alta / Media / Baja
**Estado**: Resuelto / En Progreso / Mitigado

### Descripción
Qué pasó y cómo se manifestó.

### Causa Raíz
Por qué ocurrió.

### Solución
Cómo se resolvió.

### Lecciones Aprendidas
Qué aprendimos para evitar problemas similares.
```

---

## Problemas Anticipados (Pre-mortem)

Estos son problemas que anticipamos basándonos en el análisis crítico previo a comenzar.

### P-000: Aritmética Modular Incorrecta

**Fecha**: 2026-01-28 (anticipado)
**Fase**: 0
**Severidad**: Crítica
**Estado**: Mitigado (por diseño)

### Descripción
Si generamos código C con operadores nativos (`+`, `*`), la aritmética será módulo 2^64, no módulo P del campo finito.

### Causa Raíz
C no tiene aritmética de campo finito nativa.

### Solución
DD-002: Generar `field_add`/`field_mul` en lugar de operadores nativos. Usar header configurable.

### Lecciones Aprendidas
Siempre abstraer operaciones que dependen del dominio matemático.

---

### P-001: Aliasing de Buffers

**Fecha**: 2026-01-28 (anticipado)
**Fase**: 0
**Severidad**: Alta
**Estado**: Mitigado (por diseño)

### Descripción
Si el caller pasa el mismo buffer como input y output, el código puede producir resultados incorrectos.

### Causa Raíz
Sin `restrict`, el compilador C asume que los punteros pueden aliasear.

### Solución
DD-003: Usar `restrict` en punteros de output. Agregar assertions en debug.

### Lecciones Aprendidas
Documentar y verificar contratos de memoria en código generado.

---

### P-002: Explosión de E-Graph con Vectores

**Fecha**: 2026-01-28 (anticipado)
**Fase**: 0
**Severidad**: Alta
**Estado**: Mitigado (por diseño)

### Descripción
Si el E-Graph expande vectores a elementos individuales, puede agotar memoria.

### Causa Raíz
Representación naive de operaciones vectoriales.

### Solución
DD-004: Mantener operaciones vectoriales como nodos opacos. Expandir solo en CodeGen.

### Lecciones Aprendidas
El E-Graph debe operar a nivel de abstracción correcto.

---

## Problemas Encontrados Durante Implementación

### P-003: VecExpr no está integrado con E-Graph

**Fecha**: 2026-01-28
**Fase**: 0
**Severidad**: Alta
**Estado**: Resuelto (bypass para Phase 0)

### Descripción

Al verificar la integración de `VecExpr` con el E-Graph (tarea 2 de Phase 0), se descubrió que:

1. El E-Graph existente (`EGraph/Basic.lean`) solo maneja `Expr Int` (expresiones escalares)
2. El E-Graph de matrices (`EGraph/Vector.lean`) maneja `MatExpr`, NO `VecExpr`
3. No existe ningún código que procese `VecExpr` a través del E-Graph
4. FRI fold opera sobre vectores, no matrices

Esto significa que el pipeline spec→E-Graph→CodeGen no puede funcionar para FRI fold sin trabajo adicional.

### Causa Raíz

El archivo `EGraph/Vector.lean` tiene un nombre engañoso - en realidad implementa `MatEGraph` para expresiones de matrices (`MatExpr`), no para vectores (`VecExpr`). Las expresiones vectoriales nunca fueron integradas al sistema de E-Graph.

### Análisis de Opciones

**Opción A: Crear VecEGraph**
- Implementar un E-Graph específico para `VecExpr`
- Similar a `MatEGraph` pero para operaciones vectoriales
- Pros: Diseño limpio, optimizaciones específicas para vectores
- Cons: Trabajo significativo, duplicación de código

**Opción B: Expresar vectores como matrices columna**
- Vector de n elementos → Matriz de n×1
- Usar `MatEGraph` existente
- Pros: Reutiliza infraestructura existente
- Cons: Overhead conceptual, conversiones innecesarias

**Opción C: Bypass simplificado para Phase 0**
- Para el PoC, generar código directamente desde `VecExpr` sin E-Graph
- Implementar optimizaciones básicas directamente en CodeGen
- Pros: Rápido para demostrar el concepto
- Cons: No aprovecha E-Graph, necesita refactoring posterior

### Solución Propuesta

Para Phase 0, usar **Opción C** (bypass simplificado):

1. Crear `VecCodeGen.lean` que genera C directamente desde `VecExpr`
2. Implementar `field_add`/`field_mul` según DD-002
3. Agregar `restrict` según DD-003
4. Validar con FFI según DD-005

Para fases posteriores, evaluar migración a **Opción A** o **Opción B** según necesidades de optimización.

### Lecciones Aprendidas

1. Verificar suposiciones sobre la infraestructura existente antes de planificar
2. Los nombres de archivos pueden ser engañosos - leer el código
3. Un PoC no necesita toda la infraestructura final; es mejor validar el concepto primero

---

## Estadísticas

| Severidad | Total | Resueltos | En Progreso | Mitigados |
|-----------|-------|-----------|-------------|-----------|
| Crítica | 1 | 0 | 0 | 1 |
| Alta | 3 | 1 | 0 | 2 |
| Media | 0 | 0 | 0 | 0 |
| Baja | 0 | 0 | 0 | 0 |

---

*Última actualización: 2026-01-28*
