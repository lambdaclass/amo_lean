# AMO-Lean: Documentation

## What is AMO-Lean

**AMO-Lean** = *Automatic Mathematical Optimizer in Lean*

A verified optimizing compiler that transforms mathematical specifications in Lean 4 into optimized C code with formal correctness guarantees.

```
Mathematical Spec  →  E-Graph Saturation  →  Algebraic IR  →  Optimized C
  (MatExpr)          (verified rules)      (Sigma-SPL)      (correct by construction)
```

---

## Documentation Structure

```
/                               # Repository root
├── README.md                   # Main project README (start here)
├── FAQ.md                      # 10 critical questions for ZK developers
├── RELEASE_NOTES.md            # Version history
│
├── docs/                       # Documentation directory
│   ├── README.md               # This file
│   ├── BENCHMARKS.md           # ← BENCHMARK REPORT (v1.0.1)
│   ├── sorry_elimination_plan.md  # Sorry elimination tracker
│   │
│   ├── project/                # Development documentation
│   │   ├── ROADMAP.md          # Development roadmap
│   │   ├── DESIGN_DECISIONS.md # Technical decisions (DD-001 to DD-024)
│   │   ├── PROGRESS.md         # Progress log
│   │   ├── SORRY_ELIMINATION_PLAN.md  # Detailed sorry analysis
│   │   └── Radix4/             # Radix-4 development docs
│   │
│   ├── poseidon/               # Poseidon2 documentation
│   ├── references/             # Reference material
│   └── archive/                # Obsolete documentation (historical)
```

---

## Reading Path

| Document | Audience | Purpose |
|----------|----------|---------|
| **[README.md](../README.md)** | Everyone | Project overview, quick start, architecture |
| **[FAQ.md](../FAQ.md)** | ZK/Rust developers | 10 critical questions with benchmark data |
| **[docs/BENCHMARKS.md](BENCHMARKS.md)** | Technical auditors | Complete benchmark report (2850+ tests) |
| [RELEASE_NOTES.md](../RELEASE_NOTES.md) | Contributors | Version history and changelogs |
| [project/DESIGN_DECISIONS.md](project/DESIGN_DECISIONS.md) | Contributors | 24 technical decisions with rationale |
| [project/ROADMAP.md](project/ROADMAP.md) | Contributors | Development phases and progress |

---

## Notes

- The `archive/` directory contains obsolete documents from earlier phases. Do not use for current reference.
- Benchmark data in `project/BENCHMARKS.md` is superseded by `docs/BENCHMARKS.md` (Feb 2026).

---

*AMO-Lean v1.0.1 -- Formal verification meets practical performance.*
