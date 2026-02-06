# Archivo de Documentación Histórica

Este directorio contiene documentación histórica que ha sido supersedida o consolidada.

**NO usar estos archivos como referencia actual.**

---

## Estructura del Archivo

```
archive/
├── README.md              # Este archivo
├── sessions/              # Sesiones de trabajo individuales (consolidadas)
│   ├── SORRY_ELIMINATION_SESSION_*.md (18 archivos)
│   ├── QA_CONSULT_SESSION_1.md
│   ├── QA_RESPONSE_SESSION_1.md
│   ├── QA_CONSULTATION_S12_S13.md
│   ├── QA_TEST_BATTERY_REQUEST.md
│   └── QA_REVIEW_PHASE_IMPLEMENTATION.md
├── phases/                # Planes de fases completadas
│   ├── PHASE3_COOLEY_TUKEY_STRATEGY.md
│   ├── PHASE5_NTT_PLAN.md
│   ├── PHASE5_ISSUES.md
│   ├── PHASE5_BIBLIOGRAPHY.md
│   ├── PHASE6A_PLAN.md
│   └── PHASE6B_PLAN.md
├── poseidon-phase/        # Fase Poseidon completa (Ene 26-28)
├── UNIFIED_PLAN.md        # Plan arquitectónico (consolidado en ROADMAP.md)
└── [otros archivos históricos]
```

---

## Documentos Consolidados

| Archivos Originales | Consolidado En | Fecha |
|---------------------|----------------|-------|
| 18 x `SORRY_ELIMINATION_SESSION_*.md` | `../project/SORRY_ELIMINATION_SESSIONS_UNIFIED.md` | 2026-02-06 |
| `ROADMAP.md` + `UNIFIED_PLAN.md` | `../project/ROADMAP.md` | 2026-02-06 |
| `LECCIONES_QA.md` | `../project/LEAN4_VERIFICATION_LESSONS.md` | 2026-02-06 |
| 6 x `PHASE*.md` plans | `../project/PROGRESS.md` + archivados | 2026-02-06 |

---

## Razones de Archivo

### sessions/
Las sesiones individuales (SORRY_ELIMINATION_SESSION_1 a 18) fueron consolidadas en un único archivo `SORRY_ELIMINATION_SESSIONS_UNIFIED.md` (5400+ líneas) para facilitar navegación y búsqueda.

### phases/
Los planes de fases completadas (3, 5, 6A, 6B) fueron archivados porque:
- El trabajo está completado
- Los resultados están documentados en `PROGRESS.md`
- Mantenerlos en `project/` causaba confusión sobre qué es actual

### UNIFIED_PLAN.md
Tenía ~90% de overlap con `ROADMAP.md`. Se mantuvo `ROADMAP.md` como documento oficial.

---

## Documentación Actual

Ver `docs/project/` para toda la documentación vigente:
- `ROADMAP.md` - Roadmap oficial del proyecto
- `PROGRESS.md` - Log completo de desarrollo (Phases 0-7B)
- `SORRY_ELIMINATION_SESSIONS_UNIFIED.md` - Historial completo de 18 sesiones
- `SORRY_ELIMINATION_PLAN.md` - Estado actual de sorries
- `SORRY_INVENTORY.md` - Inventario detallado
- `LEAN4_VERIFICATION_LESSONS.md` - 38 lecciones para entrenamiento

---

*Última actualización: 2026-02-06*
