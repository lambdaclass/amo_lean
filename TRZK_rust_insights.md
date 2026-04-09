# Insights: Implementar simdStmtToRust para Rust SIMD Vectorizado Verificado

**Fecha**: 2026-04-09
**Dominio**: lean4
**Estado del objeto**: Upgrade (extender verified SIMD de C NEON a Rust)

---

## 1. Análisis del Objeto de Estudio

### Resumen

Implementar `simdStmtToRust` para emitir código Rust SIMD verificado desde el mismo Stmt IR
que ya produce C NEON. El sistema cuenta con `simdStmtToC` (emisor C) y butterflies verificados
como Stmt.call (`sqdmulhButterflyStmt`, `hs2ButterflyStmt`, `hs1ButterflyStmt`). El objetivo
es crear un gemelo Rust que emita `core::arch::aarch64` intrinsics dentro de `unsafe` blocks,
permitiendo benchmark directo contra Plonky3 real (monty-31 crate).

### Keywords

simdStmtToRust, Stmt.call, NeonIntrinsic, core::arch::aarch64, unsafe blocks,
sqdmulhButterflyStmt, hs2ButterflyStmt, hs1ButterflyStmt, TrustLean.stmtToRust,
Plonky3 monty-31, widen32to64, trunc64to32, emitSIMDNTTC, int32x4_t, vqdmulhq_s32

### Estado: Upgrade

- SIMDStmtToC.lean con simdStmtToC (emisor C, línea 149-158) — EXISTE, es el template
- VerifiedSIMDButterfly.lean con butterflies Stmt.call (líneas 65-210) — EXISTE, reutilizable
- TrustLean.stmtToRust con widen/trunc correctos (commit be18f08) — EXISTE
- simdStmtToRust — **FALTA** (objetivo de este plan)
- Mapeo NeonIntrinsic → Rust intrinsic calls — **FALTA**
- Path Rust SIMD en emitSIMDNTTC — **FALTA**

---

## 2. Lecciones Aplicables

### Lecciones reutilizables

| ID | Título | Relevancia |
|----|--------|------------|
| L-730 | TrustLean dependency ≠ usage — audit pipeline wiring | **CRÍTICA**: verificar que TODO path Rust SIMD pasa por Stmt, no string emission |
| L-308 | Backend emitter architecture: 3 methods + 12 Stmt constructors | **ALTA**: simdStmtToRust debe manejar .call, .seq, delegar otros a stmtToRust |
| L-309 | Rust idioms vs C: `as usize`, `true/false`, sin parens en `if` | **ALTA**: divergencias Rust/C que afectan emisión SIMD |
| L-735 | Verificar qué tipo matchea cada función antes de estimar impacto | **MEDIA**: aplicar al auditar impacto de cambios |
| L-736 | Bridge theorems hacen inducción — siempre compilar | **MEDIA**: verificar que cambios no rompen bridges |
| L-737 | Backend-only constructors: eval como sibling más cercano | **MEDIA**: patrón usado en addrOf, reutilizable |
| L-738 | Lake default branch es master, no main | **BAJA**: ya resuelto |

### Anti-patrones a evitar

1. **L-730 (String bypass)**: NUNCA usar `partial def emitRust : String` para SIMD.
   Todo debe pasar por `Stmt.call` → `simdStmtToRust`.
2. **L-614 (String equality)**: No probar `simdStmtToRust(x) = simdStmtToC(x)`.
   Probar propiedades operacionales (void detection, intrinsic names).
3. **String patches (aprendido en v3.7.0)**: Los `.replace` en Rust fueron el primer
   red flag. No repetir — casts deben estar en el IR.

---

## 3. Bibliografía Existente Relevante

### Documentos clave

| Documento | Relevancia |
|-----------|------------|
| van der Hoeven & Lecerf (2024) — NTT implementation | Único paper con cobertura NEON aarch64 |
| HACLxN (Polubelova 2020) — Verified Generic SIMD Crypto | F★ verified SIMD para ARM Neon — patrón de referencia |
| Fiat-Crypto (Erbsen 2019) — Coq synthesis para crypto | Framework de referencia para codegen verificado |
| Almeida et al. (2023) — Kyber verified con NTT AVX2 | Gold standard de NTT SIMD formalmente verificado |
| Plonky3 Security Audit (Hepp & Richter 2024) | Única referencia Plonky3 en la biblioteca |

### Gaps bibliográficos

1. **Rust + aarch64 SIMD**: No hay papers. Documentación primaria es `core::arch::aarch64` en docs.rs.
2. **Plonky3 internals**: Solo audit report. Para benchmarking, leer el código fuente directamente
   (`plonky3/baby-bear/src/aarch64_neon/`).
3. **BabyBear/KoalaBear optimization**: No hay papers específicos para 31-bit primes.
4. **ARM NEON NTT optimization**: Cobertura limitada vs AVX2 (que tiene 5+ papers).

---

## 4. Estrategias y Decisiones Previas

### Estrategias ganadoras

1. **Stmt.call para SIMD (Option D)**: Evaluada en 6 debates adversariales.
   Reutiliza TrustLean.Stmt sin modificar. Misma strategy para Rust.
2. **NeonIntrinsic ADT como source of truth**: Elimina typos, dispatch exhaustivo.
   Extender con `toRustCall` (gemelo de `toCName`).
3. **Separar C/Rust paths**: No tocar C cuando se arregla Rust. Crear funciones
   Rust-específicas paralelas.
4. **Calibración empírica**: Benchmarkear antes de optimizar. Medir Rust SIMD vs
   C SIMD vs Plonky3 con mismo input.

### Errores evitados (aplicables)

| Error | Contexto | Aplicación |
|-------|----------|------------|
| String patches de Rust (`.replace`) | v3.7.0 — rompían cadena verificación | Ya resuelto con loadWiden/storeTrunc |
| Lazy stage truncation (u64→u32) | Rust zero-extends, C sign-extends | Verificar que SIMD Rust path no tiene el mismo issue |
| Struct output sin `&` | vst2q_s32 necesita int32x4x2_t struct | Ya resuelto con interleaveStoreHelper + addrOf |
| 11/12 Rust files defectuosos | L-730 — string emission bypassed TrustLean | Auditar todo path SIMD Rust pre-release |

### Benchmarks de referencia

| Config | Campo | N | Tiempo | vs P3 naive |
|--------|-------|---|--------|-------------|
| C NEON sqdmulh (verified) | BabyBear | 2^14 | 66.5μs | +83.8% |
| C NEON sqdmulh (legacy) | BabyBear | 2^14 | 64.0μs | +82.4% |
| C NEON Harvey | KoalaBear | 2^20 | 4027μs | +79% |
| Target: Rust NEON (nuevo) | BabyBear | 2^14 | ?μs | vs Plonky3 real |

---

## 5. Infraestructura Existente (Detallada)

### Archivos y funciones reutilizables

| Componente | Archivo : Línea | Reutilizable? |
|---|---|---|
| `NeonIntrinsic` ADT (21 constructores) | SIMDStmtToC.lean:35-64 | Sí — agregar `toRustCall` |
| `toCName` (mapeo ADT → C string) | SIMDStmtToC.lean:68-89 | Template para `toRustCall` |
| `isVoid` (void classification) | SIMDStmtToC.lean:91-94 | Sí — compartido C/Rust |
| `fromCName` (reverse map) | SIMDStmtToC.lean:119-141 | Sí — compartido |
| `neonCall` / `neonCallVoid` | SIMDStmtToC.lean:103-110 | Sí — compartido |
| `simdStmtToC` (emisor C) | SIMDStmtToC.lean:149-158 | **Template para simdStmtToRust** |
| `sqdmulhButterflyStmt` | VerifiedSIMDButterfly.lean:65-94 | Sí — Stmt puro, backend-agnostic |
| `hs2ButterflyStmt` | VerifiedSIMDButterfly.lean:111-163 | Sí — Stmt puro |
| `hs1ButterflyStmt` | VerifiedSIMDButterfly.lean:179-210 | Sí — Stmt puro |
| `deinterleaveHelperC` | SIMDEmitter.lean:546-554 | Template para Rust helper |
| `interleaveStoreHelperC` | SIMDEmitter.lean:560-569 | Template para Rust helper |
| `neonTempDecls` | SIMDEmitter.lean:575-580 | Template para Rust decls |
| `emitStageC` dispatch | SIMDEmitter.lean:393-460 | Template para Rust dispatch |
| `emitSIMDNTTC` | SIMDEmitter.lean:594-699 | Template para `emitSIMDNTTRust` |
| `emitRustFromPlanVerified` | VerifiedPlanCodeGen.lean:387-418 | Referencia para Rust scalar wrapper (transmute, declarations) |
| `UltraConfig` | UltraPipeline.lean:92-114 | Agregar flag `rustSIMD` |

### Diferencias C vs Rust para SIMD

| Aspecto | C NEON | Rust NEON |
|---------|--------|-----------|
| Header | `#include <arm_neon.h>` | `use core::arch::aarch64::*;` |
| Intrinsic call | `vqdmulhq_s32(a, b)` | `unsafe { vqdmulhq_s32(a, b) }` |
| Void call | `vst1q_s32(ptr, v);` | `unsafe { vst1q_s32(ptr, v) };` |
| Variable decl | `int32x4_t nv0;` | `let mut nv0: int32x4_t;` |
| Array access | `data[idx]` | `*data.get_unchecked(idx as usize)` o `data[idx as usize]` |
| Pointer deref | `int32_t* ptr = &data[i];` | `let ptr = data.as_ptr().add(i);` |
| Store via pointer | `*a_ptr = result;` | `unsafe { vst1q_s32(ptr, result) }` |
| Transmute | implicit cast | `std::mem::transmute` o Plonky3-style wrapping |
| Function sig | `void f(int32_t* data, ...)` | `fn f(data: &mut [u32], ...)` |

### Intrinsics: mismos nombres en C y Rust

ARM NEON intrinsics tienen **los mismos nombres** en C y Rust:
- C: `vqdmulhq_s32(a, b)` (via `arm_neon.h`)
- Rust: `vqdmulhq_s32(a, b)` (via `core::arch::aarch64`)

La diferencia es solo el wrapping: Rust necesita `unsafe { }` alrededor de cada call.

---

## 6. Infraestructura Nueva (Plan de Implementación)

### Fase 1: Bridge/SIMDStmtToRust.lean (nuevo archivo, ~120 líneas)

**Componentes**:

1. `NeonIntrinsic.toRustCall` — mapeo ADT → Rust unsafe call string.
   Mismos nombres que `toCName` pero wrapeados en `unsafe { }`:
   ```
   .sqdmulh → "unsafe { vqdmulhq_s32({args}) }"
   .store4_s32 → "unsafe { vst1q_s32({args}) }"
   ```
   Son 21 cases, mecánicos.

2. `simdStmtToRust` — emisor Rust SIMD (gemelo de `simdStmtToC`):
   ```
   | .call result fname args =>
       if void: "unsafe { fname(args) };"
       else:    "result = unsafe { fname(args) };"
   | .seq s1 s2 => ...
   | other => TrustLean.stmtToRust level other
   ```

3. Smoke tests: butterflies → simdStmtToRust → Rust string no vacío.

### Fase 2: SIMDEmitter.lean extensión (~80 líneas)

**Componentes**:

1. `neonTempDeclsRust` — declarations Rust para SIMD vars:
   ```rust
   let mut nv0: int32x4_t; let mut nv1: int32x4_t; ...
   let mut nu0: uint32x4_t; ...
   let mut nh0: int32x2_t; ...
   ```

2. `deinterleaveHelperRust` — wrapper Rust para vld2q_s32:
   ```rust
   unsafe fn neon_deinterleave_load(a: &mut int32x4_t, b: &mut int32x4_t, ptr: *const i32) {
       let tmp = vld2q_s32(ptr);
       *a = tmp.0;
       *b = tmp.1;
   }
   ```
   Nota: en Rust, `int32x4x2_t` es un tuple `(int32x4_t, int32x4_t)`, no un struct con `.val[]`.

3. `interleaveStoreHelperRust` — wrapper Rust para vst2q_s32:
   ```rust
   unsafe fn neon_interleave_store(ptr: *mut i32, a: int32x4_t, b: int32x4_t) {
       vst2q_s32(ptr, int32x4x2_t(a, b));
   }
   ```

4. `emitSIMDNTTRust` — generador Rust SIMD completo (análogo a `emitSIMDNTTC`).
   Emite: use statement + helpers + fn signature + neonTempDeclsRust + stages.

### Fase 3: UltraPipeline.lean integración (~15 líneas)

1. Agregar `rustSIMD : Bool := false` a `UltraConfig`.
2. En `ultraPipeline`, cuando `rustSIMD=true`, llamar `emitSIMDNTTRust` en vez de
   `emitRustFromPlanVerified` para generar Rust SIMD.
3. Wiring: `emit_code.lean` + `lean_driver.py` + `benchmark.py` → flag `--rust-simd`.

### Fase 4: Benchmark vs Plonky3 (~1 día)

1. Crear `Tests/benchmark/bench_plonky3_comparison/` con:
   - `Cargo.toml` dependiendo de `p3-baby-bear`, `p3-ntt`, `p3-monty-31`
   - `benches/ntt_comparison.rs` usando `criterion` para medir:
     - Plonky3 NTT (monty-31) para BabyBear
     - Nuestro NTT Rust SIMD verificado (el código generado)
2. Comparar: mismo N, mismo campo, mismo hardware.

---

## 7. Síntesis de Insights

### Hallazgos clave

1. **Los butterflies son Stmt puros** — reutilizables sin cambios entre C y Rust.
   Solo cambia el emisor final. Cero duplicación de lógica.

2. **ARM NEON intrinsics tienen los mismos nombres en C y Rust** — `toCName` es
   casi directamente reutilizable. Solo agregar `unsafe { }` wrapping.

3. **El patrón simdStmtToC es directamente clonable** — 10 líneas de lógica core
   (void detection + value-returning emission + seq + delegation).

4. **Rust NEON usa tuples, no structs** — `int32x4x2_t` en Rust es `(int32x4_t, int32x4_t)`,
   acceso via `.0/.1` no `.val[0]/.val[1]`. Los helpers necesitan adaptación.

5. **Plonky3 monty-31 es el benchmark real** — el "P3 naive" actual es un strawman.
   Con Rust SIMD verificado, podemos comparar apple-to-apple contra producción.

6. **L-730 es el riesgo principal** — asegurar que TODO el path Rust SIMD pasa por
   Stmt, no por string emission legacy.

### Riesgos identificados

1. **Unsafe proliferation**: Cada intrinsic call necesita `unsafe`. Opciones:
   (a) `unsafe` por cada call, (b) `unsafe fn` para la butterfly completa,
   (c) un `unsafe` block grande wrapeando todo el loop body.
   Recomendación: (c) — un `unsafe` block por stage, más idiomático.

2. **Pointer semantics**: C usa `int32_t*` directamente. Rust necesita raw pointers
   (`*const i32`, `*mut i32`) para pasar a intrinsics. `data.as_ptr().add(offset)`
   vs `&data[offset]`. Verificar que la emisión produce código que compila.

3. **Type mismatch signed/unsigned**: Mismo issue que en C (int32x4_t vs uint32x4_t).
   En Rust, `core::arch::aarch64` es igualmente estricto. Posiblemente necesite
   `transmute` entre `int32x4_t` y `uint32x4_t` (zero-cost en runtime).

4. **Lazy stage truncation** (de trzk_rust_fix_v2.md): En Rust scalar, lazy stages
   tenían bug de truncación u64→u32. El path SIMD no debería tener este issue
   (opera en i32/u32 nativo, sin widening a i64), pero verificar.

### Recomendaciones para planificación

1. **Empezar por Fase 1** (SIMDStmtToRust.lean) — es auto-contenido y testeable.
2. **No tocar SIMDStmtToC.lean** — crear archivo paralelo, no modificar el existente.
3. **Smoke test con Rust compilable** — no solo `lake build`, sino `rustc` real.
4. **Benchmark incremental** — primero verificar que el Rust generado compila,
   después medir performance, después comparar con Plonky3.
5. **Auditar wiring (L-730)** post-implementación — grep todo path de emisión
   Rust para verificar que no hay string bypass.

### Recursos prioritarios

1. `AmoLean/Bridge/SIMDStmtToC.lean` — template para el nuevo emisor
2. `AmoLean/EGraph/Verified/Bitwise/SIMDEmitter.lean:594-699` — pipeline C (template para Rust)
3. `AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean:387-418` — emisión Rust scalar existente
4. Rust docs: `core::arch::aarch64` — referencia de intrinsics y tipos NEON
5. Plonky3 repo: `baby-bear/src/aarch64_neon/` — implementación real a benchmarkear
