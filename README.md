# TRZK

TRZK compiles Lean specifications of zero-knowledge primitives to optimized
low-level implementations via equality saturation with hardware-aware cost
models.

This cut is a deliberately minimal end-to-end pipeline. Future growth happens
on a working foundation.

## Current abilities

- Expression language: `ArithExpr = Const Int | Var Nat | Add ArithExpr ArithExpr`
- One rewrite rule: `e + 0 → e` (right-identity)
- Rust emitter targeting `isize` arithmetic
- CLI `trzk` that turns a `.lean` spec file into a Rust function
- Integration test with crafted and fuzz vectors

## Not yet supported

Multiplication, left-identity of `+`, commutativity, constant folding, finite
fields, ZK primitives. All deferred to future iterations.

## Dependencies

Saturation is delegated to [optisat / LambdaSat](https://github.com/lambdaclass/truth_research),
a formally verified e-graph + saturation engine. We plug in via typeclass
instances; we do not reimplement the engine.

## Usage

```bash
# Build
lake build

# Compile a spec to Rust
cat > /tmp/spec.lean <<'EOF'
open TRZK (ArithExpr)
def spec : ArithExpr := .add (.var 0) (.const 0)
EOF
./.lake/build/bin/trzk /tmp/spec.lean --output /tmp/out.rs
cat /tmp/out.rs
# → pub fn arith_spec(x0: isize) -> isize { x0 }

# Run the integration test
./integration_tests/run.sh --op add0
./integration_tests/run.sh --op add0 --fuzz -n 1000
```

## Pipeline

Four stages, each with one owner:

1. **Parse** — Lean itself. The user writes `def spec : ArithExpr := ...` in a
   `.lean` file; the CLI runs it via `lake env lean --run`.
2. **Saturate** — optisat. Our `ArithOp` type plugs in via `NodeOps` and
   `Extractable` typeclass instances.
3. **Emit** — hand-rolled Rust emitter (`TRZK/Emit.lean`).
4. **Execute** — scripted harness (`integration_tests/`).

See [`docs/pipeline.md`](docs/pipeline.md) for details.

## Layout

| Path | Purpose |
|------|---------|
| `TRZK/ArithExpr.lean` | AST users write specs in |
| `TRZK/ArithOp.lean` | e-graph node + optisat typeclass instances |
| `TRZK/Rule.lean` | rewrite rule registry |
| `TRZK/Pipeline.lean` | embed + optimize |
| `TRZK/Emit.lean` | Rust emitter |
| `Compile.lean` | trzk CLI |
| `Tests/*.lean` | `#guard` tests |
| `integration_tests/` | end-to-end harness |
| `docs/` | pipeline, saturation, onboarding, glossary |

## License

See [`LICENSE`](LICENSE).
