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

## Notas Específicas

- Bibliografía adicional: `~/Documents/claudio/biblioteca/ntt/`

## Protocolo Lean 4

**Continuidad**: Leer CLAUDE.md + ARCHITECTURE.md → identificar fase/nodo actual → CONTINUAR (NO re-planificar). Solo `/plan-project` si el usuario lo pide o tarea NUEVA sin plan. NO crear fases/subfases nuevas sobre plan activo.

**Scout**: `python3 ~/.claude/skills/plan-project/scripts/scout.py --targets "{nodos}" {archivos}` OBLIGATORIO antes de cada bloque. Code Map (~2-3K tok), NO archivos completos.

**Ejecución**: Hojas → paralelo (≥2). Intermedios → paralelo (≥3), secuencial si menos. Fundacionales/Críticos → SIEMPRE secuencial + firewall `_aux`. Gates → de-risk con sketch antes de dependientes.

**Firewall `_aux`**: (1) `theorem nombre_aux` flexible (2) probar sin tocar original (3) migrar cuando compile (4) `lake build` completo.

**Escalación** (hooks enforzan): Directo (1-2) → `/ask-dojo` (3) → `/ask-lean` (4) → reformular.

**Checkpoints** (hook cada 3 edits): HOJA `lake env lean {f}` | INTERMEDIO + dependientes | FUNDACIONAL `lake build`.

**Verificación post-nodo** (OBLIGATORIA al completar cada nodo del DAG):
1. `verify_node.py --project {path} --files {archivos} --node "{nombre}"` — checks mecánicos (0 LLM tokens)
2. Si mecánicos PASS → QA riguroso via subagente: `collab.py --rounds 1 --detail full` — stress, casos borde, robustez, hipótesis redundantes, calidad de pruebas, coherencia con ARCHITECTURE.md
3. Si QA encuentra problemas → resolver ANTES de continuar. Guardar lección en ARCHITECTURE.md.
4. Registrar resultados en BENCHMARKS.md (sección del nodo, orden topológico).

**Patrones**: Fuel explícito (`Nat`), nunca well-founded sobre mutable. `Array.set` funcional. foldl con tipos explícitos en lambdas. Doc comments solo en `def`/`theorem`/`lemma`/`structure`.

**Recursos**: Bibliografía `~/Documents/claudio/biblioteca/`, Lecciones `~/Documents/claudio/lecciones/lean4/` (INDEX.md → selectiva), Índices `~/Documents/claudio/biblioteca/indices/`.

**Skills**: `/ask-lean`, `/ask-dojo`, `/lean4-theorem-proving`, `/lean-search`, `/lean-check`, `/lean-goal`, `/lean-diagnostics`. Plugins cameronfreer: proof-search, tactic, error-diagnosis, refactoring, documentation.

## Hooks (advisory pero de cumplimiento OBLIGATORIO)

Los hooks emiten advertencias o bloqueos. **Seguirlos es obligatorio, sin excepciones:**

| Hook | Trigger | Acción requerida |
|---|---|---|
| `warn-large-read.sh` | Read de source/md >200 líneas sin offset | **BLOQUEADO**. Usar scout.py primero, luego Read con offset+limit |
| `suggest-scout-on-grep.sh` | Grep en directorios source | Considerar scout.py para búsquedas estructurales |
| `guard-block-close.sh` | Edit de ✓ en ARCHITECTURE.md | Ejecutar close_block.py + QA primero |

**Si un hook emite una advertencia o bloqueo, DETENER y seguir las instrucciones del hook antes de continuar.**

## Rúbrica de benchmarks (durante PLANIFICACIÓN, antes de ejecutar)

Al planificar con `/plan-project`, ANTES de iniciar la ejecución:
1. `/benchmark-qa --strict` → Gemini genera la rúbrica (criterios + targets + metodología)
2. Documentar la rúbrica en `BENCHMARKS.md` sección "Criterios"
3. La rúbrica es el contrato: los bloques se evalúan contra ella al cerrar

**La rúbrica se diseña UNA VEZ al planificar, NO al cerrar. Esto optimiza tokens.**

## Cierre de bloque (OBLIGATORIO)

ANTES de marcar un bloque/nodo como completado:
1. `close_block.py --project . --block "Bloque N" --nodes '{...}'`
2. Ejecutar benchmarks contra la rúbrica ya existente en `BENCHMARKS.md`
3. Si PASS → QA riguroso (`/collab-qa`)
4. Si QA PASS → registrar resultados en `BENCHMARKS.md` → ENTONCES marcar ✓

## Cierre de fase (OBLIGATORIO)

ANTES de cerrar una fase completa:
1. Benchmarks finales comprehensivos contra la rúbrica
2. Registrar lecciones en `ARCHITECTURE.md`
3. Tag de versión

**NUNCA cerrar bloque ni fase sin ejecutar benchmarks contra la rúbrica.**
