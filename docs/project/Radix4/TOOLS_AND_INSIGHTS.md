# Herramientas e Insights - Proyecto NTT Radix-4

## Herramientas de Desarrollo

### 1. Orquestador de Agentes IA

**Ubicación**: `~/lean4-agent-orchestra/`

**Flujo de trabajo híbrido**:
- **Claude Code**: Planificación, implementación, debugging
- **Gemini API**: Revisión QA de planes

**Scripts útiles**:
```bash
# Enviar plan a revisión QA
python3 qa_review.py --file plan.md

# Buscar bibliografía relevante
python3 bib_search.py --query "NTT formal verification" --max 5
```

### 2. Búsqueda Bibliográfica

**Fuentes**:
- arXiv (categorías: cs.LO, cs.PL, math.LO)
- Semantic Scholar

**Comando**:
```bash
python3 bib_search.py --query "Lean 4 theorem proving tactics"
```

### 3. Revisión QA con Gemini

**Modelo**: gemini-2.0-flash

**Uso**:
```bash
python3 qa_review.py --file plan.md --request "Contexto adicional"
```

**Veredictos posibles**:
- APROBAR: Listo para implementar
- REVISAR: Ajustes menores necesarios
- RECHAZAR: Cambios fundamentales requeridos

---

## Papers Relevantes Encontrados

### LLMs para Theorem Proving

| Paper | Año | Citas | Relevancia |
|-------|-----|-------|------------|
| **LeanDojo** | 2023 | 342 | Playground open-source para Lean 4 |
| **DeepSeek-Prover** | 2024 | 158 | LLM entrenado para Lean 4 |
| **DeepSeek-Prover-V1.5** | 2024 | 134 | RL desde feedback del proof assistant |
| **DeepSeek-Prover-V2** | 2025 | 120 | Descomposición en subgoals |
| **Kimina-Prover** | 2025 | 90 | 72B params, reasoning-driven |

### Paper Fundacional
**"The Lean 4 Theorem Prover"** (2021)
- Autores: L. de Moura, S. Ullrich
- Citas: 420
- Describe arquitectura extensible de Lean 4

---

## Insights del Estudio Bibliográfico

### Del libro A=B

1. **Hipergeometricidad**
   - Los términos `ω^(nk)` son hipergeométricos
   - Ratio: `ω^(n(k+1))/ω^(nk) = ω^n` es constante
   - Habilita uso de series geométricas

2. **WZ-Pairs**
   - Certificados compactos para identidades
   - Potencial para automatización futura
   - No implementado actualmente en Mathlib

3. **q-Análogos**
   - Framework natural para F_p
   - Raíces de unidad = caso especial q = ω

4. **Ortogonalidad**
   - Clave para roundtrip: `Σ ω^(nk) = N·δ(n,0)`
   - Conecta con polinomios ortogonales (Chebyshev)

### De los PDFs del proyecto

1. **CRT-based proof strategy**
   - Factorizar `X^N - 1 = Π(X - ω^k)`
   - NTT = evaluación en raíces

2. **Butterfly4 matrix T₄**
   - Matriz explícita 4×4
   - ψ = ω^(N/4), ψ² = -1
   - Verificable entrada por entrada

3. **ψ² = -1 property**
   - Fundamental para simplificar butterfly4
   - Se deduce de `ω^(N/2) = -1`

---

## Lecciones Aprendidas del QA

### Feedback Valioso de Gemini

| Versión | Feedback Clave | Acción |
|---------|---------------|--------|
| v3 | "A=B provee intuición, no automatización" | Clarificar en documentación |
| v4 | "INTT no definida" | Añadir definición explícita |
| v4 | "División por N requiere precondición" | Añadir `N.Coprime p` |
| v5 | "Casos base deben ser explícitos" | Documentar NTT_spec_one |

### Patrones de Revisión QA

1. **Primera revisión**: Problemas estructurales
2. **Segunda revisión**: Detalles de implementación
3. **Tercera revisión**: Edge cases y robustez

---

## Estrategias de Prueba Identificadas

### Para Sumas Finitas

```lean
-- Separar en pares/impares
rw [sum_split_even_odd]

-- Reindexar
apply Finset.sum_bij

-- Intercambiar orden
rw [Finset.sum_comm]
```

### Para Potencias de ω

```lean
-- Simplificar ω^(a*b)
ring

-- Usar ω^N = 1
simp [hω.pow_eq_one]

-- Usar ω^(N/2) = -1
rw [hω.pow_eq_neg_one]
```

### Para Matrices 4×4

```lean
-- Verificar entrada por entrada
ext i j
fin_cases i <;> fin_cases j <;> simp [...]
```

### Para Inducción

```lean
-- Inducción fuerte
induction N using Nat.strong_induction_on with
| _ N ih => ...

-- Terminación explícita
termination_by n => n
```

---

## Configuración del Entorno

### APIs Configuradas

```bash
# ~/.../lean4-agent-orchestra/.env
ANTHROPIC_API_KEY=sk-ant-...  # Para Claude (si se usa API)
GOOGLE_API_KEY=AIzaSy...       # Para Gemini QA
```

### Dependencias Python

```bash
pip3 install python-dotenv google-generativeai arxiv semanticscholar
```

### Verificación

```bash
# Probar Gemini QA
python3 qa_review.py --plan "Test" --request "Prueba"

# Probar búsqueda bibliográfica
python3 bib_search.py --query "Lean 4" --max 2
```

---

## Próximos Pasos Sugeridos

1. **Investigar Mathlib** (Fase 0)
   - Buscar lemas de `IsPrimitiveRoot`
   - Verificar `geom_sum_eq` disponible

2. **Implementar lemas fundamentales** (Fase 1)
   - Comenzar con `roots_of_unity_sum`
   - Es el lema más crítico

3. **Iterar con QA**
   - Enviar código parcial para revisión
   - Ajustar según feedback

4. **Documentar progreso**
   - Actualizar `IMPLEMENTATION_LOG.md`
   - Marcar tareas completadas en `WORKPLAN.md`
