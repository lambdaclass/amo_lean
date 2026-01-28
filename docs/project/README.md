# AMO-Lean: Automatic Mathematical Optimizer

**AMO-Lean es un optimizador formal escrito en Lean.**

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
| 2 | Reglas de Optimización | ✅ COMPLETADA |
| 3 | CodeGen SIMD | 🔄 SIGUIENTE |
| 4 | API Producción | ⏳ Pendiente |

---

## Documentación

| Documento | Propósito |
|-----------|-----------|
| **[ROADMAP.md](ROADMAP.md)** | **Plan oficial** - fases, entregables, criterios de éxito |
| [DESIGN_DECISIONS.md](DESIGN_DECISIONS.md) | Decisiones técnicas (DD-001 a DD-006) |
| [PROGRESS.md](PROGRESS.md) | Log de trabajo completado |
| [BENCHMARKS.md](BENCHMARKS.md) | Resultados de rendimiento |
| [TESTING_ANALYSIS.md](TESTING_ANALYSIS.md) | Análisis de testing |

---

## Métricas Actuales

| Métrica | Valor |
|---------|-------|
| Tests | 120/120 pass |
| Speedup Lean→C | 32.3x |
| Goldilocks throughput | 568 M elem/s |
| **Optimization reduction** | **91.67%** |
| Fases completadas | 3 de 4 |

---

*AMO-Lean: Automatic Mathematical Optimizer in Lean*
