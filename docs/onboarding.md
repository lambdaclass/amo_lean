# Onboarding

## Build

```bash
lake update       # once, to resolve optisat
lake build        # builds TRZK, Tests, and the trzk binary
```

The first build compiles optisat transitively (~40 jobs, a few minutes).
Subsequent builds are incremental.

## Run unit tests

```bash
lake build Tests
```

Any failing `#guard` breaks the build. Test modules live in `Tests/`:

- `Tests/ArithExpr.lean` — AST size + structural checks
- `Tests/Pipeline.lean` — end-to-end `optimize` behavior
- `Tests/Emit.lean` — exact emitted strings

## Run the integration test

```bash
./integration_tests/run.sh --size 1                  # crafted vectors
./integration_tests/run.sh --size 1 --fuzz -n 1000   # random fuzz
```

The script builds `trzk`, compiles `arith_spec_1.lean` to Rust, links the
harness, and pipes test vectors to the verifier.

## Add a new spec

1. Write `integration_tests/my_spec.lean`:
   ```lean
   open TRZK (ArithExpr)
   def spec : ArithExpr := .add (.var 0) (.var 1)
   ```
2. Compile: `./.lake/build/bin/trzk integration_tests/my_spec.lean --output /tmp/my.rs`
3. Inspect: `cat /tmp/my.rs` and `cat integration_tests/artifacts/my.{pre,post}.txt`

## Add a new rewrite rule

Edit `TRZK/Rule.lean` only. The shape is:

```lean
def myRule : RewriteRule ArithOp where
  name := "my_rule"
  lhs := .node (.add 0 0) [.patVar 0, .patVar 0]   -- x + x
  rhs := .node (.add 0 0) [.node (.const 2) [], .patVar 0]  -- 2 * x (if mul existed)

def allRules : List (RewriteRule ArithOp) := [addZeroRight, myRule]
```

No edits to `Pipeline.lean`, `ArithOp.lean`, or `Emit.lean` are needed.

Add `#guard` cases to `Tests/Pipeline.lean` to pin the new behavior.
