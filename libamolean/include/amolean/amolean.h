/**
 * AMO-Lean: Automatic Mathematical Optimizer in Lean
 *
 * Header-only C library for formally verified mathematical operations.
 * All optimizations are verified correct using Lean 4 theorem proofs.
 *
 * Copyright (c) 2026 AMO-Lean Project
 * Licensed under MIT License
 *
 * Version: 0.1.0
 */

#ifndef AMOLEAN_H
#define AMOLEAN_H

#ifdef __cplusplus
extern "C" {
#endif

/* Version information */
#define AMOLEAN_VERSION_MAJOR 0
#define AMOLEAN_VERSION_MINOR 1
#define AMOLEAN_VERSION_PATCH 0
#define AMOLEAN_VERSION "0.1.0"

/* Feature detection */
#if defined(__x86_64__) || defined(_M_X64)
  #define AMOLEAN_ARCH_X86_64 1
  #if defined(__AVX2__)
    #define AMOLEAN_HAS_AVX2 1
  #endif
#elif defined(__aarch64__) || defined(_M_ARM64)
  #define AMOLEAN_ARCH_ARM64 1
#endif

/**
 * Core includes - always available
 */
#include "field_goldilocks.h"

/* Compatibility: GOLDILOCKS_P is an alias for GOLDILOCKS_ORDER */
#ifndef GOLDILOCKS_P
  #define GOLDILOCKS_P GOLDILOCKS_ORDER
#endif

/**
 * SIMD includes - available on x86-64 with AVX2
 */
#ifdef AMOLEAN_HAS_AVX2
  #include "field_goldilocks_avx2.h"
  #include "fri_fold_avx2.h"
#endif

/**
 * FRI operations - scalar version always available
 */
#include "fri_fold.h"

#ifdef __cplusplus
}
#endif

#endif /* AMOLEAN_H */
