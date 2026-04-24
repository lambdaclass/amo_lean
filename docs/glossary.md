# Glossary

- **ArithExpr** — TRZK's user-facing AST (`TRZK/ArithExpr.lean`).
  Tree-shaped: `Const Int | Var Nat | Add ArithExpr ArithExpr`.
- **ArithOp** — TRZK's e-graph node type (`TRZK/ArithOp.lean`).
  Flat: children are `EClassId`s, not subtrees. Distinct from `ArithExpr`
  because optisat's engine wants flat nodes; we bridge with `Extractable`.
- **E-graph** — a data structure storing many equivalent expressions
  compactly, as a set of e-classes each containing one or more e-nodes.
- **E-class** — an equivalence class of terms. Identified by an `EClassId`.
- **E-node** — a concrete `Op` instance whose children are e-class ids.
- **Saturation** — repeatedly applying rewrite rules, each match adding new
  e-nodes and merging equivalent e-classes, until the graph stabilizes or
  fuel runs out.
- **Rewrite rule** — a `RewriteRule Op` pairing an `lhs` pattern with an
  `rhs` pattern. Patterns are `.patVar i` (variable placeholder) or
  `.node op [children]`.
- **Extraction** — picking a lowest-cost representative from each e-class,
  yielding a concrete term. We use optisat's `extractAuto`.
- **optisat / LambdaSat** — the upstream verified saturation engine
  (`https://github.com/lambdaclass/truth_research`), pinned via `lakefile.toml`.
