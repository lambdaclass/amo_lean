# Saturation

TRZK does not implement saturation itself. It delegates to
[optisat / LambdaSat](https://github.com/lambdaclass/truth_research), pinned at
a specific commit in `lakefile.toml`.

## What optisat gives us

- `EGraph Op` — an e-graph parameterized by an `Op` node type (with `children`,
  `mapChildren`, `replaceChildren`, `localCost` provided via the `NodeOps`
  typeclass).
- `RewriteRule Op` — pattern-based rewrite rules. Patterns are `.patVar i` or
  `.node op [children]`.
- `saturateF fuel maxIter rebuildFuel g rules` — fuel-bounded saturation loop.
- `computeCostsF g cost fuel` — cost-model evaluation.
- `extractAuto g root` — lowest-cost extraction from an e-class.

## Brief primer

An **e-graph** is a data structure for storing many equivalent expressions
compactly. Each **e-class** represents an equivalence class of terms; its
**e-nodes** are concrete `Op` instances whose children are e-class ids.

**Saturation** repeatedly applies rewrite rules: every rule match adds new
e-nodes and merges e-classes that become provably equal. When the graph
stabilizes (or fuel runs out), we **extract** the lowest-cost representative
of each class.

## Why a verified backend

Optisat ships proofs that saturation preserves the semantics of the starting
term (modulo a `NodeSemantics` instance). This cut does not yet invoke that
theorem — we use optisat purely for its operational correctness — but the
proof is available for future work.

## Further reading

- `/Users/pelito/Code/truth_research/ARCHITECTURE.md` — optisat internals
- `/Users/pelito/Code/truth_research/LambdaSat/SaturationSpec.lean` — saturation spec
- `/Users/pelito/Code/truth_research/LambdaSat/Extraction.lean` — extraction
