# Referencias Bibliográficas - AMO-Lean

Este directorio contiene papers y documentación técnica relevante para el desarrollo de AMO-Lean.

## Organización

```
references/
├── poseidon/    # Hash ZK-friendly (Prioridad #1)
├── gpu/         # Backend CUDA (Prioridad #2)
└── fri/         # Protocolo FRI y STARKs
```

## Papers Clave por Componente

### Poseidon Hash (Prioridad #1)

| Paper | Autores | Relevancia |
|-------|---------|------------|
| **Poseidon: A New Hash Function for Zero-Knowledge Proof Systems** | Grassi et al. (USENIX 2021) | Paper principal, define MDS matrices y S-boxes |
| **Rescue-Prime: a Standard Specification** | Aly et al. | Alternativa a Poseidon, comparar trade-offs |
| **Algebraic Attacks on Round-Reduced Poseidon** | Varios | Entender seguridad y por qué se eligen ciertos parámetros |

**Links:**
- Poseidon paper: https://eprint.iacr.org/2019/458.pdf
- Poseidon spec (Filecoin): https://spec.filecoin.io/algorithms/crypto/poseidon/
- Implementación referencia: https://github.com/filecoin-project/neptune

### Backend CUDA/GPU (Prioridad #2)

| Paper | Autores | Relevancia |
|-------|---------|------------|
| **Montgomery Multiplication on GPUs** | Emmart et al. | Aritmética modular eficiente en GPU |
| **Optimizing Parallel Reduction in CUDA** | Harris (Nvidia) | Patrones fundamentales de GPU |
| **Better Performance at Lower Occupancy** | Volkov | Optimización contra-intuitiva de GPU |

**Links:**
- CUDA Programming Guide: https://docs.nvidia.com/cuda/cuda-c-programming-guide/
- cuFHE (referencia): https://github.com/vernamlab/cuFHE

### FRI Protocol

| Paper | Autores | Relevancia |
|-------|---------|------------|
| **Fast Reed-Solomon IOP of Proximity** | Ben-Sasson et al. (ICALP 2018) | Paper original de FRI |
| **STARK Paper** | Ben-Sasson et al. | Contexto de uso de FRI |
| **Proximity Gaps for Reed-Solomon Codes** | Ben-Sasson et al. | Análisis de seguridad |

**Links:**
- FRI paper: https://eccc.weizmann.ac.il/report/2017/134/

## Cómo Añadir Referencias

1. Descarga el PDF al directorio apropiado
2. Nombra el archivo descriptivamente: `autor_año_titulo_corto.pdf`
3. Actualiza este README con un resumen
4. Opcionalmente, añade notas en `notes.md` dentro del subdirectorio

## Formato de Notas

Cada subdirectorio puede tener un `notes.md` con:
- Resumen ejecutivo del paper
- Secciones relevantes para AMO-Lean
- Decisiones de diseño que implica
- Código/pseudocódigo extraído
