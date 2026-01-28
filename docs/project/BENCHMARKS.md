# AMO-Lean Option A: Benchmarks

**Última actualización**: 2026-01-28

Este documento registra todos los benchmarks de rendimiento.

---

## Metodología

### Hardware
- Plataforma: macOS Darwin 24.6.0 (Apple Silicon)

### Software
- Lean 4.x
- Compilador: gcc/clang
- Flags: `-O3 -march=native` (release), `-fsanitize=address,undefined` (test)

### Proceso
1. 10 iteraciones de warmup
2. N iteraciones de medición
3. Checksum para evitar dead code elimination
4. Timing: `IO.monoNanosNow` (Lean), `clock_gettime` (C)

---

## Phase 0: FRI Fold (UInt64)

**Operación**: `out[i] = even[i] + alpha * odd[i]`
**Campo**: UInt64 nativo (wrapping arithmetic)

| Size | Iterations | Lean (ns) | C (ns) | Speedup |
|------|------------|-----------|--------|---------|
| 16 | 100,000 | 28,458,167 | 673,000 | **42.3x** |
| 64 | 50,000 | 36,833,958 | 1,033,000 | **35.7x** |
| 256 | 10,000 | 24,049,709 | 832,000 | **28.9x** |
| 1,024 | 5,000 | 44,471,458 | 1,630,000 | **27.3x** |
| 4,096 | 1,000 | 36,084,667 | 1,316,000 | **27.4x** |

**Average Speedup: 32.3x**

### Análisis Phase 0
- Speedup disminuye con tamaño (42x → 27x): overhead se amortiza
- C mantiene ventaja consistente ~27x a escala

---

## Phase 1: FRI Fold (Goldilocks)

**Operación**: `out[i] = (even[i] + alpha * odd[i]) mod p`
**Campo**: Goldilocks p = 2^64 - 2^32 + 1

| Size | Iterations | UInt64 (μs) | Goldilocks (μs) | Overhead |
|------|------------|-------------|-----------------|----------|
| 16 | 100,000 | 539 | 2,894 | **5.4x** |
| 256 | 50,000 | 4,430 | 23,763 | **5.4x** |
| 1,024 | 10,000 | 4,054 | 19,910 | **4.9x** |
| 4,096 | 5,000 | 18,371 | 127,695 | **6.9x** |

### Throughput

| Implementación | Throughput |
|----------------|------------|
| UInt64 | ~2,000-3,000 M elem/s |
| Goldilocks | ~400-570 M elem/s |

**Overhead promedio: ~5x**

### Análisis Phase 1
- Overhead 5x es aceptable para aritmética de campo real
- Throughput 400+ M elem/s sigue siendo muy alto
- Overhead mayor en tamaños grandes debido a cache effects

### Por qué Goldilocks es más lento
1. Multiplicación 128-bit
2. Reducción especializada (split, shift, subtract)
3. Adición segura con cast a 128-bit

### Comparación con expectativas
| Implementación | Overhead Esperado | Overhead Real |
|----------------|-------------------|---------------|
| Barrett Reduction | 10-15x | N/A (no usado) |
| Goldilocks Specialized | 3-8x | 5x ✅ |

---

## Resumen de Speedups

| Métrica | Valor |
|---------|-------|
| Lean → C (UInt64) | **32.3x** |
| UInt64 → Goldilocks overhead | **5x** |
| Lean → C (estimado con Goldilocks) | **~6.5x** |

---

## Reproducción

```bash
# Phase 0 benchmark
lake build phase0-bench
./.lake/build/bin/phase0-bench

# Phase 1 benchmark
cd generated
gcc -O3 -march=native -o bench_goldilocks_fri bench_goldilocks_fri.c
./bench_goldilocks_fri [size] [iterations]

# Sanitizer tests
./run_sanitizer_tests.sh
```

---

## Benchmarks Futuros (Phase 2+)

| Benchmark | Métrica | Estado |
|-----------|---------|--------|
| Optimization: Naive vs Optimized | % reducción de ops | ⏳ Pendiente |
| SIMD: AVX2/AVX512 | Speedup vs scalar | ⏳ Pendiente |
| vs HorizenLabs/poseidon2 | Relative performance | ⏳ Pendiente |

---

*Documento de benchmarks de AMO-Lean Option A*
