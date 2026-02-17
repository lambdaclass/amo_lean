# AMO-Lean: Formal Optimization Library

## Proyecto

Biblioteca de optimización formal en Lean 4. Campos finitos verificados (Goldilocks, BabyBear), codegen Rust, verificación Kron.
- **Dominio**: lean4
- **Toolchain**: leanprover/lean4:v4.26.0
- **Mathlib**: v4.26.0
- **Config**: lakefile.lean
- **Compilar**: `lake build` (completo) o `lake env lean {archivo}` (individual)

## Estado Actual

- **v2.1.0**: Lean 4.26.0, Mathlib v4.26.0
- Fase 9 (Migración 4.16→4.26): COMPLETADA — Subfases 1-8, `lake build` 3134 jobs, 0 errores
- Verified E-Graph engine: 13 archivos, 4,594 LOC, 121 teoremas, zero sorry
- Roadmap migración: `amo-lean_v2.0.0.md`

## Recursos del Dominio

- **Bibliografía**: `~/Documents/claudio/biblioteca/{criptografia,matematica,ntt,optimizacion}/`
- **Lecciones**: `~/Documents/claudio/lecciones/lean4/` (INDEX.md → carga selectiva por L-ID)
- **Índices**: `~/Documents/claudio/biblioteca/indices/`

## Skills Lean 4

| Necesidad | Skill |
|-----------|-------|
| Planificación | `/plan-project --domain lean4` |
| Búsqueda proyecto actual (LSP) | `/lean-search`, `/lean-check`, `/lean-diagnostics` |
| Búsqueda Mathlib (87K teoremas) | `/ask-dojo` |
| Estrategia de prueba (DeepSeek) | `/ask-lean` |
| QA colaborativo | `/collab-qa` |
| Lecciones | `/load-lessons lean4` |
| Benchmark | `/benchmark-qa` |

## Continuidad de Sesión

**REGLA**: Al iniciar sesión, ANTES de hacer cualquier cosa:
1. Leer el roadmap activo (`amo-lean_v2.0.0.md` o el más reciente en `docs/`)
2. Identificar la fase/subfase actual y las tareas pendientes
3. **CONTINUAR desde donde se quedó** — NO re-planificar con /plan-project
4. Solo invocar `/plan-project` si el usuario lo pide explícitamente o si hay una tarea NUEVA sin plan

**NO re-planificar trabajo existente.** Si el usuario dice "continuemos", leer el plan y ejecutar el siguiente paso pendiente. Crear nuevas fases/subfases sobre un plan activo destruye la nomenclatura y el progreso.

## Protocolo de Ejecución

### Scout Phase (OBLIGATORIO antes de cada bloque de trabajo)
```bash
python3 ~/.claude/skills/plan-project/scripts/scout.py \
  --targets "{nodos_a_trabajar}" --context-lines 5 {archivos}
```
Genera Code Map (~2-3K tok, 0 LLM). Trabajar con el Code Map, NO leer archivos completos.

### Modo de ejecución por tipo de nodo
- **Hojas** (sin dependientes): Agent Teams en paralelo si ≥2 nodos independientes
- **Intermedios**: Agent Teams si ≥3 nodos, secuencial si menos
- **Fundacionales/Críticos**: SIEMPRE secuencial, con firewall `_aux`
- **Gates**: De-risk con sketch ANTES de trabajar en dependientes

### Protocolo fundacional (firewall _aux)
1. Crear `theorem {nombre}_aux` con signatura flexible
2. Probar `_aux` sin tocar original
3. Migrar solo cuando compile sin sorry
4. `lake build` completo después

### Escalación (hooks E/F lo enforzan automáticamente)
- Intentos 1-2: resolver directamente con Code Map
- Intento 3: `/ask-dojo` para buscar en Mathlib
- Intento 4: `/ask-lean` con contexto del error
- Si persiste: reformular nodo (cambiar signatura, agregar hipótesis)

### Checkpoints de compilación (hook H enforza cada 3 edits)
- HOJA → `lake env lean {archivo}`
- INTERMEDIO → `lake env lean {archivo}` + dependientes
- FUNDACIONAL/CRÍTICO → `lake build` completo

### Otros hooks activos
- Hook C: advierte lectura de archivos >200 líneas → usar scout.py
- Hook G: advierte edición sin `_aux` en archivos con alto fan-out
- Hook I: sugiere branch al primer edit de la sesión
