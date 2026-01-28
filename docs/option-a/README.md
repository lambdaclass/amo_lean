# AMO-Lean Option A: Optimización Formal

**AMO-Lean Option A es un compilador optimizador formal.**

```
Spec Matemática  →  E-Graph Saturation  →  Código C Optimizado
  (MatExpr)          (reglas verificadas)   (correcto por construcción)
```

---

## Estado Actual

| Fase | Descripción | Estado |
|------|-------------|--------|
| 0 | Proof of Concept | ✅ COMPLETADA |
| 1 | Goldilocks Field | ✅ COMPLETADA |
| 2 | Reglas de Optimización | 🔄 EN CURSO |
| 3 | CodeGen SIMD | ⏳ Pendiente |
| 4 | API Producción | ⏳ Pendiente |

---

## Documentación

| Documento | Propósito |
|-----------|-----------|
| **[ROADMAP.md](ROADMAP.md)** | **Plan oficial y único** - fases, entregables, criterios de éxito |
| [DESIGN_DECISIONS.md](DESIGN_DECISIONS.md) | Decisiones técnicas (DD-001 a DD-006) |
| [PROGRESS.md](PROGRESS.md) | Log de trabajo completado |
| [BENCHMARKS.md](BENCHMARKS.md) | Resultados de rendimiento |
| [TESTING_ANALYSIS.md](TESTING_ANALYSIS.md) | Análisis de testing y cobertura |

---

## Regla de Oro

> **ROADMAP.md es el documento autoritativo.**
> Si hay conflicto entre documentos, el ROADMAP tiene precedencia.

---

## Métricas Actuales

| Métrica | Valor |
|---------|-------|
| Tests | 98/98 pass |
| Speedup Lean→C | 32.3x |
| Goldilocks throughput | 568 M elem/s |
| Fases completadas | 2/4 |

---

## Cómo Contribuir

1. Leer [ROADMAP.md](ROADMAP.md) para entender el plan actual
2. Ver [PROGRESS.md](PROGRESS.md) para trabajo en curso
3. Documentar decisiones en [DESIGN_DECISIONS.md](DESIGN_DECISIONS.md)
4. Registrar benchmarks en [BENCHMARKS.md](BENCHMARKS.md)

---

*AMO-Lean Option A: Optimización Formal de Primitivos Criptográficos*
