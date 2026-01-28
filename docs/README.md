# AMO-Lean: Documentación

## Qué es AMO-Lean

**AMO-Lean** = *Automatic Mathematical Optimizer in Lean*

Un optimizador formal que toma especificaciones matemáticas y genera código C optimizado con garantías de corrección.

```
Spec Matemática  →  E-Graph Saturation  →  Código C Optimizado
  (MatExpr)          (reglas verificadas)   (correcto por construcción)
```

---

## Estructura de Documentación

```
docs/
├── README.md                    # Este archivo
├── project/                     # ← DOCUMENTACIÓN PRINCIPAL
│   ├── README.md               # Overview del proyecto
│   ├── ROADMAP.md              # ** ROADMAP OFICIAL **
│   ├── DESIGN_DECISIONS.md     # Decisiones técnicas
│   ├── PROGRESS.md             # Log de progreso
│   ├── BENCHMARKS.md           # Resultados de rendimiento
│   └── TESTING_ANALYSIS.md     # Análisis de testing
├── archive/                     # Documentación obsoleta (no usar)
├── references/                  # Material de referencia
└── poseidon/                    # Docs de Poseidon (caso de prueba)
```

---

## Documentación Principal

| Documento | Propósito |
|-----------|-----------|
| **[project/ROADMAP.md](project/ROADMAP.md)** | **Plan oficial** - fases, entregables, criterios |
| [project/README.md](project/README.md) | Overview y estado actual |
| [project/DESIGN_DECISIONS.md](project/DESIGN_DECISIONS.md) | Decisiones técnicas |
| [project/PROGRESS.md](project/PROGRESS.md) | Log de trabajo completado |
| [project/BENCHMARKS.md](project/BENCHMARKS.md) | Resultados de rendimiento |

---

## Material de Referencia

| Documento | Propósito |
|-----------|-----------|
| [poseidon/](poseidon/) | Documentación de Poseidon2 (caso de prueba) |
| [references/](references/) | Papers y notas de referencia |
| [LEGACY_STATUS.md](LEGACY_STATUS.md) | Estado histórico (contexto) |

---

## Nota Importante

> **El roadmap oficial está en `project/ROADMAP.md`.**
>
> La carpeta `archive/` contiene documentos obsoletos que causaron
> confusión anteriormente (múltiples roadmaps, "Option A", etc.)

---

*AMO-Lean: Automatic Mathematical Optimizer in Lean*
