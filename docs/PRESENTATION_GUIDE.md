# Guía de Documentación para Presentaciones

**Última actualización**: 2026-01-30
**Versión**: v0.7.0 (Phase 6B)

---

## Para tu Jefe (Resumen Ejecutivo)

### Archivo Principal
**`README.md`** (raíz del proyecto)

Contiene:
- Qué es AMO-Lean
- Resultados de performance vs Plonky3
- Estado de verificación formal
- Casos de uso

### Puntos Clave a Resaltar

1. **Verificación Formal**: 95% de reglas E-Graph probadas en Lean
2. **Compatibilidad Plonky3**: 64/64 tests de equivalencia
3. **Performance**: 70% del throughput de Plonky3 manteniendo garantías formales
4. **Tests**: 1481+ tests pasando

---

## Para Colegas Técnicos

### Archivos Recomendados (en orden)

| # | Archivo | Contenido | Tiempo de lectura |
|---|---------|-----------|-------------------|
| 1 | `README.md` | Overview general | 5 min |
| 2 | `RELEASE_NOTES.md` | Qué hay de nuevo en v0.7.0 | 3 min |
| 3 | `docs/project/PROGRESS.md` | Historia completa de desarrollo | 15 min |
| 4 | `docs/project/PHASE6B_PLAN.md` | ADRs y decisiones técnicas | 20 min |

### Para Deep-Dive Técnico

| Tema | Archivo |
|------|---------|
| Análisis de Plonky3 | `docs/project/PLONKY3_ANALYSIS.md` |
| Diseño de Phase 3 (AVX2) | `docs/project/PHASE3_DESIGN.md` |
| Bibliografía NTT | `docs/project/PHASE5_BIBLIOGRAPHY.md` |
| Decisiones de diseño | `docs/project/DESIGN_DECISIONS.md` |
| Plan unificado | `docs/project/UNIFIED_PLAN.md` |

---

## Benchmarks Específicos a Resaltar

### NTT Performance vs Plonky3

```
┌──────────┬─────────────┬─────────────┬────────────┐
│   Size   │  Plonky3    │  AMO-Lean   │ Throughput │
├──────────┼─────────────┼─────────────┼────────────┤
│ N=256    │    4.1 μs   │    5.9 μs   │   70%      │
│ N=1024   │   14.5 μs   │   22.4 μs   │   65%      │
│ N=65536  │ 1402.7 μs   │ 2398.7 μs   │   58%      │
└──────────┴─────────────┴─────────────┴────────────┘
```

### Verificación

| Métrica | Valor |
|---------|-------|
| Oracle tests vs Plonky3 | **64/64 PASS** |
| Hardening tests | **120/120 PASS** |
| FFI overhead | **0.03%** |
| Reglas E-Graph verificadas | **19/20 (95%)** |
| Teoremas NTT | **71/80 (89%)** |

### Mejoras Phase 6B

| Optimización | Impacto |
|--------------|---------|
| Pre-alloc work buffer | +19% throughput |
| Tabla bit-reversal | +24 puntos porcentuales |
| Full twiddle caching | +7-11% |
| Loop unrolling x4 | +2-4% |

---

## Ubicación de Archivos

### En Disco Local

```
/Users/manuelpuebla/Documents/claudio/amo-lean/
├── README.md                    ← PRESENTACIÓN PRINCIPAL
├── RELEASE_NOTES.md             ← NOTAS DE VERSIÓN
└── docs/
    └── project/
        ├── PROGRESS.md          ← HISTORIA COMPLETA
        ├── PHASE6B_PLAN.md      ← DECISIONES TÉCNICAS
        ├── PLONKY3_ANALYSIS.md  ← ANÁLISIS TÉCNICO
        └── ROADMAP.md           ← ROADMAP OFICIAL
```

### En GitHub

Una vez subido, los archivos estarán en:
```
https://github.com/[usuario]/amo-lean/blob/main/README.md
https://github.com/[usuario]/amo-lean/blob/main/RELEASE_NOTES.md
https://github.com/[usuario]/amo-lean/blob/main/docs/project/PROGRESS.md
```

---

## Archivos a EVITAR

Estos archivos están archivados o son material de referencia:

| Ubicación | Razón |
|-----------|-------|
| `docs/archive/*` | Documentación obsoleta |
| `docs/*.pdf` | Papers de referencia (no son del proyecto) |
| `docs/optimizaciones prefase5/` | Notas de investigación |
| `verification/plonky3/plonky3_source/` | Código externo de Plonky3 |

---

## Presentación Rápida (5 minutos)

Si solo tienes 5 minutos para presentar:

1. **Qué es**: Compilador verificado que transforma specs matemáticas en código C optimizado
2. **Diferenciador**: Garantías formales de corrección (proofs en Lean)
3. **Resultado**: 70% de Plonky3 con verificación matemática
4. **Tests**: 1481+ tests, 64/64 compatibilidad con Plonky3
5. **Estado**: Production-ready (v0.7.0)

---

## Contacto para Dudas

Ver issues en GitHub o contactar al equipo de desarrollo.
