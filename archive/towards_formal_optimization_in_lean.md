# AMO-Lean: Formal Program Optimization via Equality Saturation in Dependent Types

*By [Your Name/Organization]*

Traditional verified compilers, such as CompCert, focus on semantic preservation of already-written C code, limiting their ability to perform radical algorithmic optimizations. On the other hand, domain-specific code generators like SPIRAL produce extremely efficient code but lack formal correctness guarantees integrated into the proof assistant.

AMO-Lean is an optimization engine implemented natively in Lean 4 that combines both traditions. The system compiles algebraic theorems from Mathlib into rewrite rules that feed a purely functional equality saturation engine, and emits C code with SIMD intrinsics accompanied by formal traceability annotations (*Proof Anchors*).

The result is an optimizer where every applied transformation has a corresponding Lean proof, and where the emitted code can be audited against the formally verified logic.

In what follows, we dissect the four architectural pillars of the system.


## 1. The Algebraic DSL: SPIRAL Lifted to Type Theory

### What is a DSL and Why We Need One

A DSL (*Domain-Specific Language*) is a programming language designed for a specific domain, in contrast to a general-purpose language like Rust or C. A DSL does not need to handle threads, I/O, or memory management — it only needs to precisely express the operations of its domain. In exchange for this restriction, it gains a property: the compiler can reason exhaustively about programs written in it, because the space of possible programs is bounded and structured.

In AMO-Lean, the DSL is a Lean 4 inductive type called `MatExpr`. It is the intermediate representation on which the entire system operates: rewrite rules are applied on it, the E-Graph stores it, and codegen translates it to C. A program in this DSL does not describe *how* to compute a transform — it describes *what* transform it is, as an algebraic formula. The optimizer is responsible for deriving the *how*.

### SPIRAL: Optimization as Matrix Algebra

To understand the DSL, one must first understand SPIRAL.

SPIRAL is a project from Carnegie Mellon (Franchetti, Püschel et al.) that tackles a specific problem: generating highly optimized code for linear transforms (FFT, NTT, DCT, WHT) without writing implementations by hand. The core idea is that all these transforms can be represented as products of structured sparse matrices, and that optimizations — reordering operations, vectorizing, improving cache locality — are equivalent to applying algebraic identities on those matrices.

SPIRAL's insight is that an FFT of size $N$ is not an algorithm: it is a factorization. The Cooley-Tukey identity makes this explicit:

$$DFT_{mn} = (DFT_m \otimes I_n) \cdot D_n^{mn} \cdot (I_m \otimes DFT_n) \cdot L_n^{mn}$$

This says: to compute a DFT of size $m \times n$, apply a stride permutation ($L$), then $n$ small DFTs of size $m$ in parallel ($I_m \otimes DFT_n$), then multiply by twiddle factors ($D$), then $m$ DFTs of size $n$ in parallel ($DFT_m \otimes I_n$). Each factor is a sparse matrix with exploitable structure.

The central operator is the **Kronecker Product** $A \otimes B$. If $A$ is $m \times m$ and $B$ is $n \times n$, then $A \otimes B$ is an $(mn) \times (mn)$ matrix that applies $A$ to "blocks" and $B$ within each block. In code terms, $I_m \otimes A_n$ is a `for` loop of $m$ iterations applying $A$ to contiguous segments of size $n$. And $A_m \otimes I_n$ is the same operation but with interleaved (*strided*) data. SPIRAL transforms between these two forms using stride permutations, choosing whichever maps better to the hardware.

What AMO-Lean adopts from SPIRAL:

1. **Representation**: transforms are matrix formulas, not imperative code.
2. **Optimization by algebraic rewriting**: optimizing means applying identities (Cooley-Tukey, stride factorization, Kronecker distribution).
3. **Lowering pipeline**: the algebraic formula is lowered to a Σ-SPL intermediate representation with explicit loops, and from there to C with SIMD.

What AMO-Lean adds: in SPIRAL, the algebraic identities are axioms *hardcoded* in the compiler (written in GAP/OCaml). If an identity has an error, the compiler silently generates incorrect code. In AMO-Lean, each identity is a theorem verified by the Lean 4 kernel.

### Types and Constructors: The Structure of the DSL

For readers familiar with `enum` in Rust, a Lean inductive type is conceptually similar: it defines a closed type with a finite set of *variants* (called **constructors**). The difference is that in Lean, constructors can be **indexed by values** — the matrix dimensions are part of the type, not runtime data.

AMO-Lean's DSL defines `MatExpr α m n`: a matrix expression over a coefficient type `α`, with `m` rows and `n` columns. The main constructors are:

```lean
inductive MatExpr (α : Type) : Nat → Nat → Type where
  | identity (n : Nat) : MatExpr α n n             -- I_n
  | dft (n : Nat) : MatExpr α n n                  -- Symbolic DFT
  | ntt (n p : Nat) : MatExpr α n n                -- NTT over Z_p
  | twiddle (n k : Nat) : MatExpr α n n            -- Twiddle factors
  | perm : Perm n → MatExpr α n n                  -- Permutation
  | kron : MatExpr α m₁ n₁ → MatExpr α m₂ n₂      -- A ⊗ B
         → MatExpr α (m₁ * m₂) (n₁ * n₂)
  | compose : MatExpr α m k → MatExpr α k n        -- A · B
            → MatExpr α m n
  | add : MatExpr α m n → MatExpr α m n            -- A + B
        → MatExpr α m n
  -- ... and others
```

Two points to note:

1. **Dimensions are part of the type.** `compose` only accepts matrices where the inner dimension $k$ matches — $A_{m \times k} \cdot B_{k \times n}$. Lean rejects a composition with incompatible dimensions at compile time. This is impossible to express in a Rust `enum` without resorting to `PhantomData` and complex trait bounds.

2. **Symbolic constructors do not expand.** `dft 1024` does not store a $1024 \times 1024$ matrix of entries — it is a single node that *represents* that transform. The Cooley-Tukey factorization applied to `dft 1024` produces a tree of ~$\log_2(1024) = 10$ levels with `kron`, `compose`, `twiddle`, and `perm`. This keeps the representation at $O(\log N)$ nodes for a transform of size $N$, which is what allows the E-Graph to operate efficiently on large transforms.

### Symbolic Permutations

The operator $L_n^{mn}$ (stride permutation) models memory reorderings. Concretely, it maps index $i$ to $(i \bmod m) \cdot n + \lfloor i / m \rfloor$, which is the transpose of an $m \times n$ matrix stored in row-major order.

Instead of emitting copy code immediately, AMO-Lean keeps permutations as symbolic data (`Perm.lean`), composing and simplifying them algebraically before code generation. Permutations are also an inductive type indexed by their size:

```lean
inductive Perm : Nat → Type where
  | identity : Perm n
  | stride : (m n : Nat) → Perm (m * n)
  | bitRev : (k : Nat) → Perm (2^k)
  | compose : Perm n → Perm n → Perm n
  | tensor : Perm m → Perm n → Perm (m * n)
  -- ...
```

The module includes formal proofs of key algebraic properties:
- **Stride inversion**: `stride_inverse_eq` proves that $L_n^{mn} \cdot L_m^{mn} = I_{mn}$, proved by modular arithmetic on the indices.
- **Bit-reversal as involution**: `bitReverse_involution` proves that applying bit-reversal twice is the identity. The proof proceeds by induction on the number of bits, with auxiliary lemmas decomposing the relationship between the most significant and least significant bits of the result.
- **Tensor product distribution**: `tensor_compose_pointwise` proves that $(P_1 \otimes Q_1) \cdot (P_2 \otimes Q_2) = (P_1 \cdot P_2) \otimes (Q_1 \cdot Q_2)$, a fundamental identity for reordering SPIRAL operations.

The difference from SPIRAL is that these identities are not implicit compiler axioms, but verified theorems in Lean. With one exception that must be documented: the tensor product of permutations requires a computationally verifiable axiom (`applyIndex_tensor_eq`) due to a limitation of the Lean 4 kernel with the *splitter* for indexed inductive types. The axiom states that `applyIndex (tensor p q) i` computes the same result as an auxiliary function `applyTensorDirect` — both definitions are algorithmically identical, but Lean cannot automatically generate the equation for pattern matching over the indexed type `Perm n`. The axiom is exhaustively validated by `#eval` for all concrete sizes used in the system.


## 2. The Equality Saturation Engine

### What is an E-Graph

To understand equality saturation, one must first understand the problem it solves.

Consider an optimizer with two rules: $a \times 1 \to a$ and $a \times (b + c) \to a \times b + a \times c$. Given the expression $x \times (1 + y)$, a conventional rewriter must choose which rule to apply first. If it applies distribution, it gets $x \times 1 + x \times y$, and can then simplify to $x + x \times y$. But if another rule directly simplified $1 + y$, the decision to distribute first might have been suboptimal. The problem is that conventional rewriting is **destructive**: applying a rule discards the original expression. The result depends on the application order, and finding the optimal order is in general an exponential search problem.

An **E-Graph** (*Equality Graph*) solves this by *simultaneously* representing all equivalent forms of an expression. It is a data structure that stores a set of expressions grouped into **equivalence classes**: if two expressions have been proven equal, they belong to the same class.

Concretely, an E-Graph has two components:

1. **E-Nodes**: nodes representing operations. An e-node for $a + b$ stores the operator `+` and references to the *classes* of $a$ and $b$ (not to concrete nodes). This is key: since children point to classes, not to specific expressions, a single e-node for `+` implicitly represents the sum of *any* pair of representatives of those classes.

2. **E-Classes**: sets of e-nodes that have been proven equivalent. When a rewrite rule establishes that $e_1 = e_2$, the e-nodes of $e_1$ and $e_2$ are merged into the same class.

**Equality saturation** is the process of applying *all* rewrite rules exhaustively until none produces new equivalences (fixed point) or a limit is exceeded. The result is not an optimal expression — it is an E-Graph containing *all* discovered equivalent expressions. Then, an **extraction** phase selects the best one according to a cost model.

The advantage: the order of rule application is irrelevant. All rules are applied in logical parallel. There is no backtracking.

### An E-Graph in a Pure Functional Language

The reference implementation of E-Graphs is [`egg`](https://egraphs-good.github.io/) (Willsey et al., 2021), written in Rust. `egg` uses `Vec<T>` with indices as implicit pointers, leveraging Rust's controlled mutability for efficient merge operations.

Implementing the same structure in Lean 4 — a pure functional language — presents distinct design challenges. Lean guarantees referential purity: there is no observable mutation, no pointers, no aliasing. This is what enables the Lean kernel to verify proofs, but it also means that cyclic or densely linked data structures must be designed carefully to avoid excessive pressure on memory management.

In `EGraph/Basic.lean`, AMO-Lean avoids recursive inductive structures (trees, linked lists of nodes) that would be the idiomatic choice in Lean. Instead, it uses an architecture of **flat hash tables with integer indices** — conceptually closer to an ECS (*Entity-Component-System*) than to a functional graph:

- **Nodes as flat data**: An `ENode` stores an operation and the `EClassId` (alias for `Nat`) of its children. It contains no recursive substructures:

  ```lean
  inductive ENodeOp where
    | const : Int → ENodeOp
    | var : Nat → ENodeOp
    | add : EClassId → EClassId → ENodeOp
    | mul : EClassId → EClassId → ENodeOp
    | pow : EClassId → Nat → ENodeOp
  ```

- **Hashconsing**: A `Std.HashMap ENode EClassId` guarantees structural uniqueness of nodes. If two subexpressions are structurally identical, they share the same e-node. This enables $O(1)$ equivalence checks by integer identifier comparison.

- **Union-Find with path compression**: The equivalence class structure is managed via a union-find implemented over `Array EClassId`, with path compression during `find`. Lean 4 internally implements a *reference counting* mechanism: when an `Array` has a single owner (refcount = 1), operations like `set!` mutate in-place without copying. This provides performance comparable to the mutable case for the union-find usage pattern, where the array is modified sequentially within a function.

This architecture avoids cycles in the heap and maintains the referential purity required by the Lean kernel. The matrix E-Graph (`EGraph/Vector.lean`) extends this same design with `MatENodeOp` nodes that include Kronecker products, permutations, twiddle factors, and transposition operations as first-class variants.

### Saturation and E-Matching

The saturation engine (`Saturate.lean`) is a pure function:

```lean
def saturate (g : EGraph) (rules : List RewriteRule)
    (config : SaturationConfig) : SaturationResult
```

There is no global state, no monads, no side effects. The E-Graph goes in, the saturated E-Graph comes out. Each iteration applies all rules over all classes, instantiates the right-hand sides that match, merges the corresponding classes, and executes `rebuild` to restore the hashcons invariants. The process terminates when a fixed point is reached or a configurable limit on nodes/iterations is exceeded.

The `EMatch.lean` module implements **e-matching**: given an LHS pattern (e.g., `?a * (?b + ?c)`) and an E-Graph class, the matcher searches for all assignments of the pattern variables (`?a`, `?b`, `?c`) that make the pattern match some node in the class. When it finds one, the system instantiates the RHS with those assignments, adds the result to the graph, and merges the LHS class with the RHS class.

Note what *does not* happen: the original node is not destroyed. The merge only establishes that two classes are equivalent. This is what makes equality saturation non-destructive and independent of rule application order.

**Controlling combinatorial explosion.** There are rules that threaten to grow the E-Graph indefinitely. Commutativity ($a + b \to b + a$) applied once produces a new expression; applied again, it regenerates the original; and so on in an infinite cycle. AMO-Lean implements two strategies in `Optimize.lean`:

1. **Directed rules**: Each `OptRule` has a classification (`.reducing`, `.structural`, `.expanding`) and a `costDelta` that estimates whether the rule reduces or increases the expression's cost. Only *reducing* rules are in the safe set by default.
2. **Canonical ordering**: For commutative operations, a deterministic structural hashing (`exprHash`) imposes a preferred ordering on operands: if `hash(a) > hash(b)`, only `a + b` is stored, never `b + a`. This eliminates the need for a bidirectional commutativity rule. The tradeoff is explicit: theoretical completeness is sacrificed (the E-Graph will not explore *all* possible commuted forms) in exchange for guaranteed termination. In practice, for the signal processing optimizations we target, this tradeoff is acceptable.


## 3. The Trust Bridge: Verified Rules and MetaM

In most compilers, optimizations ($x \times 0 \to 0$, factorization, distribution) are implicit assumptions in the compiler's C++ code. If a rule is incorrect, the compiler silently produces wrong code. There is no mechanism within the compiler to *prove* that the transformation preserves program meaning.

In AMO-Lean, every rewrite rule has a corresponding Lean theorem proving preservation of denotational semantics. And the mechanism that connects those theorems to the optimizer — the one that converts formal proofs into executable rules — is the metaprogramming monad `MetaM`.

### Structure of a Verified Rule

As defined in `VerifiedRules.lean`, a rule consists of:

1. A syntactic pattern (LHS → RHS).
2. A formal theorem of semantic equality:
   $$\forall \, \texttt{env}, \; \texttt{eval}(\texttt{env}, \texttt{LHS}) = \texttt{eval}(\texttt{env}, \texttt{RHS})$$

For example, distributivity:

```lean
theorem distrib_left_correct (env : VarId → Int) (a b c : Expr Int) :
    eval env (.mul a (.add b c)) = eval env (.add (.mul a b) (.mul a c)) := by
  simp only [eval]
  ring
```

The structure of this proof is representative. The `eval` function is the **denotational semantics** of the DSL: it translates a syntactic expression (`Expr Int`) to its semantic value (`Int`) given a variable environment. The `simp only [eval]` unfolds the recursive definition of `eval`, reducing both sides to pure arithmetic expressions over integers. The `ring` tactic — provided by Mathlib — closes the goal automatically because the resulting equality is a ring identity.

The simpler proofs (identities involving 0 and 1) use Mathlib lemmas directly: `Int.add_zero`, `Int.mul_one`, `zero_mul`, `add_zero`. Ring properties (distributivity, associativity) are closed with `ring`. Power proofs require induction over lists (`foldl`). AMO-Lean does not reimplement arithmetic: it *imports* existing Mathlib lemmas and uses them as the foundation of correctness.

Of the system's 20 rewrite rules, 19 are formally verified without `sorry`. The remaining rule (`zero_pow` for the general case) has a theorem with the $n+1$ case fully proved (`zero_pow_succ_correct`).

### MetaM: What It Is and What It Enables

Here we arrive at the component that distinguishes AMO-Lean from a conventional optimizer that merely *has* proofs: the ability to **automatically convert theorems into rewrite rules**.

To understand why this matters, consider the alternative. Without metaprogramming, each optimizer rule is written by hand twice: once as `Pattern → Pattern` for the E-Graph, and once as a theorem for the correctness proof. If the two definitions diverge — if the pattern says `a * (b + c) → a*b + a*c` but the theorem proves something else — the system is inconsistent without anyone noticing. This is exactly the kind of subtle error that formal verification should prevent.

`MetaM` is Lean 4's metaprogramming monad. For Rust readers, a monad is similar to a trait like `Future` or `Iterator` that encapsulates a computation pattern; in this case, `MetaM` encapsulates computations that have access to *Lean's compiler internal state*. Concretely, a function operating in `MetaM` can:

- **Query the environment**: Access all definitions, theorems, and axioms loaded in the current context. This includes all of Mathlib. The function `getConstInfo name` returns the complete declaration of any constant by its name — its type, its body, its universe levels.

- **Inspect the internal representation of expressions**: In Lean, everything — types, terms, proofs — is represented as values of type `Lean.Expr`. An expression like `a + b = b + a` is internally an application of `@Eq` to a type, with subexpressions that are applications of `@HAdd.hAdd` with type arguments and typeclass instances. `MetaM` allows navigating this structure, decomposing it, and reconstructing it.

- **Open quantifiers**: A theorem like `∀ (a b : α), a + b = b + a` in its internal representation is a chain of `Lean.Expr.forallE`. The function `forallTelescope` opens all quantifiers simultaneously, creating fresh free variables for each one and exposing the equality body. This allows inspecting the LHS and RHS of the conclusion without having to manually parse the chain of `forallE`.

- **Resolve metavariables**: `instantiateMVars` substitutes pending metavariables (unknowns) in an expression with their assignments. This is necessary because Lean's elaborator may leave metavariables unresolved during incremental elaboration.

### How AMO-Lean Uses MetaM

The module `Meta/CompileRules.lean` defines a monad transformer `ConvertM := StateT ConvertState MetaM` that combines MetaM with its own state for variable tracking. The complete pipeline for converting a theorem into a rewrite rule is:

1. **Obtain the theorem's type**: `getConstInfo name` retrieves the declaration. The type of a theorem *is* its statement — for example, the type of `distrib_left_correct` is `∀ env a b c, eval env (.mul a (.add b c)) = eval env (.add (.mul a b) (.mul a c))`.

2. **Open the quantifiers**: `forallTelescope type fun args body` opens all the `∀`s and exposes `body`, which is an equality `Eq lhs rhs`.

3. **Extract LHS and RHS**: `extractEqualityFromExpr` uses `e.eq?` — a MetaM helper that recognizes the structure `@Eq.{u} α lhs rhs` — to obtain both sides of the equality.

4. **Convert to Pattern**: `exprToPatternAux` recursively traverses the `Lean.Expr` of the LHS (and the RHS), recognizing applications of known functions:
   - `@HAdd.hAdd _ _ _ _ e₁ e₂` → `Pattern.add p₁ p₂`
   - `@HMul.hMul _ _ _ _ e₁ e₂` → `Pattern.mul p₁ p₂`
   - `@HPow.hPow _ _ _ _ base (lit n)` → `Pattern.pow p n`
   - `Lean.Expr.fvar id` → `Pattern.patVar n` (where `n` is assigned sequentially per variable)
   - `OfNat.ofNat _ (lit v) _` → `Pattern.const v`

   Note that the function recognizes both the "heterogeneous" versions (`HAdd.hAdd` with 6 arguments) and the "homogeneous" versions (`Add.add` with 4 arguments) of each operator. This is necessary because Lean elaborates `a + b` differently depending on context.

5. **Emit the rule**: The result is a `RewriteRule` with name, LHS pattern, and RHS pattern, ready to be consumed by the E-Graph.

All of this is invoked with the `#compile_rules` command:

```lean
#compile_rules [distrib_left_correct, mul_one_right_correct, add_zero_left_correct]
```

The command iterates over the names, executes the pipeline for each one, and emits the compiled rules with a diagnostic log. If a theorem does not have the expected form (is not an equality, or uses unsupported operators), it emits a `logWarning` instead of failing silently.

### Advantage for the Project

The advantage of this approach is not just convenience. It is **structural consistency**: the rules that the E-Graph applies are mechanically extracted from the same theorems that prove their correctness. There is no possibility of divergence between "what the optimizer believes is correct" and "what is formally proven." If someone modifies a theorem in Mathlib or in the project, `#compile_rules` automatically extracts the new version.

Furthermore, MetaM opens the door to a capability that conventional optimizers lack: generating rewrite rules from *any* equality theorem in Mathlib, without manual intervention. In principle, every algebraic identity that Mathlib knows — and Mathlib knows thousands — is a potential optimization for the E-Graph. The current module supports the scalar DSL operators (addition, multiplication, exponentiation); extending it to the matrix DSL operators from SPIRAL is work in progress.

### Rewriter Correctness

The central correctness theorem (`Correctness.lean`) is structured in layers:

1. `applyFirst_sound`: if all rules in a list preserve semantics, applying the first one that matches also preserves semantics.
2. `rewriteBottomUp_sound`: bottom-up rewriting preserves semantics (by structural induction on the expression).
3. `rewriteToFixpoint_sound`: iteration to fixed point preserves semantics (by induction on fuel).
4. `simplify_sound`: the main simplification function preserves semantics, composing the previous lemmas with `algebraicRules_sound`.

This result is formally proven for the scalar rewriter. For the E-Graph engine, correctness reduces to the correctness of individual rules: since every rule applied during saturation has an independent proof, and the `merge` operation only adds equivalences without destroying nodes, the extracted result preserves the semantics of the input. The full formalization of this compositional argument for the E-Graph is work in progress.

### CI Auditing

The system includes an audit function (`auditOptRules`) that verifies at compile time that each optimizer rule has a corresponding theorem. A `#guard` in `VerifiedRules.lean` fails the build if the count of verified rules does not match the expected value.


## 4. Code Generation, Cost Model, and Proof Anchors

### From Algebra to Silicon: The Lowering Pipeline

Code generation follows SPIRAL's three-stage pipeline:

1. **MatExpr → Σ-SPL** (`Sigma/Basic.lean`): Matrix formulas are lowered to the Sigma-SPL intermediate representation, which explicitly models memory access patterns. A Kronecker product $I_n \otimes A_m$ transforms into a loop: $\Sigma_{i=0}^{n-1} (S_{i,m} \cdot A \cdot G_{i,m})$, where $G$ is a *gather* (read with stride) and $S$ is a *scatter* (write with stride).

2. **Σ-SPL → expanded Σ-SPL** (`Sigma/Expand.lean`): Composite operations are expanded to elementary operations with concrete indices.

3. **Σ-SPL → C** (`Sigma/CodeGen.lean`, `Sigma/SIMD.lean`): The final code is emitted as scalar C or with SIMD intrinsics. Vectorization follows SPIRAL's principle: $A \otimes I_\nu$ (where $\nu$ is the SIMD width) vectorizes trivially — each scalar operation becomes a SIMD operation.

### Cost Model and Extraction

Once the E-Graph is saturated, the system contains a superposition of equivalent implementations. The original expression and all expressions discovered by rewrite rules coexist in the graph. Extracting the "best" requires a criterion: that is the cost model.

The `MatCostModel` is a parameterizable SIMD-aware structure:

```lean
structure MatCostModel where
  simdWidth : Nat := 4         -- 4 for AVX2, 8 for AVX-512
  identityCost : Nat := 0      -- Free: generates no code
  dftSymbolicCost : Nat := 0   -- Symbolic: will be expanded later
  nttSymbolicCost : Nat := 0   -- Symbolic
  twiddleCost : Nat := 1       -- Diagonal multiplication (/ simdWidth)
  permCost : Nat := 2          -- Data movement
  kronCost : Nat := 0          -- Symbolic
  composeCost : Nat := 1       -- Composition
  addCost : Nat := 1           -- Matrix addition
  smulCost : Nat := 1          -- Scalar multiplication
  transposeCost : Nat := 2     -- Transposition
  scalarPenalty : Nat := 1000  -- Penalty: scalar fallback
```

The design decisions are deliberate:

1. **Symbolic operations cost zero.** A `dft 1024` node generates no code by itself — it will be expanded in later pipeline stages. Assigning it zero cost in the E-Graph means the extractor will never prefer a premature expansion over the factored representation. This preserves the $O(\log N)$ structure that SPIRAL needs.

2. **Costs scaled by SIMD width.** The cost of twiddle factors and element-wise operations (`elemwise`) is divided by `simdWidth`. This reflects that an AVX2 vector multiplication processes 4 elements at the cost of one instruction. The consequence: when changing `simdWidth` from 4 to 8, the extractor automatically prefers factorizations with greater internal parallelism.

3. **Scalar fallback penalty.** The `scalarPenalty := 1000` is an explicit anti-pattern: if the E-Graph contains a variant requiring scalar expansion (without vectorization), the extractor avoids it at all costs. This steers the search without needing negative rules.

The extraction algorithm is a bottom-up iterative analysis (`computeCosts`): for each e-class, the cost of each node is evaluated as `localCost + Σ childCosts`, and the minimum-cost node is recorded. The process iterates until convergence (fixed point) or a maximum of 100 iterations, necessary because dependencies between classes can be circular.

This design has a property worth making explicit: **the cost model is the only unverified component that affects result quality.** The rewrite rules are formally proven — any expression extracted from the E-Graph is semantically correct. But the *optimality* of the generated code depends entirely on the costs reflecting hardware reality. An incorrect cost model produces correct but slow code.

### Proof Anchors

AMO-Lean introduces the concept of *Proof Anchors* in the generated code.

The emitted C code includes structured annotations documenting the preconditions, postconditions, and invariants of each block:

```c
// PROOF_ANCHOR: fri_fold_parametric
// Preconditions:
//   - n > 0
//   - even, odd, out are non-null
//   - out does not alias even or odd (required for restrict)
// Postconditions:
//   - forall i in [0, n): out[i] == even[i] + alpha * odd[i]
//   - output array is fully initialized
```

These annotations create a traceability chain connecting the algebraic transformations verified in Lean to specific blocks of emitted code. They are not executable assertions nor end-to-end formal verification of the binary — they are structured documentation designed to facilitate human auditing and future integration with static verification tools.

The difference from an ad-hoc comment is that Proof Anchors are generated *systematically* by the codegen pipeline (controlled by the `proofAnchors` flag in `CodeGenConfig`) and follow a parseable format, enabling external tools to extract them and cross-reference them against the Lean project's theorems.

A verified binary is useless if it is not auditable. Proof Anchors are AMO-Lean's mechanism for making the distance between the formal proof and the executed code auditable.


## 5. Portability and Connections to the State of the Art

AMO-Lean's architecture — a typed DSL, an E-Graph with verified rules, a parameterizable cost model, and a codegen pipeline with traceability — is not specific to the matrix domain. The components are separable, and the natural question is: to what other domains can this pattern be applied?

### The General Pattern

The pattern that AMO-Lean instantiates is:

1. Define a DSL as a Lean inductive type (with denotational semantics).
2. Write rewrite rules as semantic preservation theorems.
3. Compile those rules to an E-Graph via MetaM.
4. Saturate, extract with a cost model, and emit code.

To apply this to a different domain, it suffices to replace `MatExpr` with another DSL and write the corresponding rules. The E-Graph, union-find, hashconsing, saturation, and extraction are generic — they assume nothing about the domain except that nodes have children and a cost.

The most direct candidates are domains where known algebraic identities exist and where the "best" implementation depends on context (hardware, input size, required precision):

- **Arithmetic circuits over finite fields.** The optimization of R1CS (*Rank-1 Constraint Systems*) for ZK presents an analogous structure: a single computation admits multiple representations as constraint systems, and the choice affects the number of constraints and, therefore, the proof cost. Wang et al. (RNA, 2024) observe that "there are significant differences in the R1CS forms generated from programs with the same underlying semantics" — exactly the scenario where equality saturation provides value. To date, there is no published work applying E-Graphs to ZK circuit optimization; this is an open problem.

- **Dense linear algebra.** SPORES (Wang et al., VLDB 2020) already demonstrates this: it converts linear algebra expressions to relational algebra, optimizes with equality saturation, and converts back. The rewrite rules are complete (any equivalent LA expression is reachable). AMO-Lean's cost model could be instantiated for this domain by replacing `MatCostModel` with BLAS operation costs.

- **Numerical precision.** Herbie (Panchekha et al., PLDI 2015, under active development) uses equality saturation via egglog to explore mathematically equivalent floating-point expressions and select the most numerically precise one. The objective function there is not performance but numerical error — a case where the "cost function" is radically different from ours, but the E-Graph machinery is identical.

### The Extraction Problem as Combinatorial Optimization

Extraction — selecting the best expression from a saturated E-Graph — is NP-hard in general and hard to approximate within a constant factor (Goharshady et al., OOPSLA 2024, Distinguished Paper). This has direct consequences for AMO-Lean's portability to domains with larger E-Graphs.

AMO-Lean's current extractor uses a greedy bottom-up algorithm (similar to egg's): for each e-class, it chooses the node with minimum local cost + child costs. This algorithm is optimal when the E-Graph is a DAG, but can produce suboptimal results when there are shared subexpressions (*common subexpressions*): the same node can be a child of multiple e-classes, and greedy extraction cannot capture this interaction.

The state of the art offers several alternatives, none of which eliminates the tension between optimality and efficiency:

- **ILP (Integer Linear Programming).** TENSAT (Yang et al., MLSys 2021) applies equality saturation to deep learning computation graphs and uses ILP for extraction. This guarantees optimality but scales poorly: TENSAT needs to prune cycles from the E-Graph as preprocessing to reduce ILP solving time.

- **Differentiable extraction.** SmoothE (Cai et al., ASPLOS 2025) makes extraction differentiable, enabling gradient-based optimization. It outperforms heuristic extractors on adversarial datasets where greedy fails due to common subexpressions.

- **Parameterized treewidth.** Goharshady et al. (OOPSLA 2024) prove that extraction is polynomial for E-Graphs with bounded treewidth, and present a parameterized algorithm implemented in Rust that is optimal up to treewidth 10.

For AMO-Lean in its current domain (fixed-size transforms with recursive structure), the greedy extractor is sufficient: the E-Graphs resulting from SPIRAL factorizations are trees or shallow DAGs with limited sharing. But if the system is ported to domains with greater sharing (arithmetic circuits, neural network computation graphs), the choice of extractor becomes a non-trivial architectural decision.

### Learned Cost Models

A research direction directly relevant to AMO-Lean is replacing the manual cost model with a learned one:

- Singh (Cambridge, 2022) models equality saturation as an MDP (*Markov Decision Process*) and uses PPO (*Proximal Policy Optimization*) to learn which rules to apply and when to stop saturation.
- E-morphic (DAC 2025) uses a GNN (*Graph Neural Network*) to estimate circuit costs during extraction, trained on the OpenABC-D benchmark.
- MCTS + EqSat (PACT 2024) uses Monte Carlo Tree Search to guide both E-Graph construction and extraction, improving neural network inference speedup by up to 11%.

The implication for AMO-Lean is concrete: the `MatCostModel` is currently a table of hand-written constants. If `localCost : MatENode → Nat` is replaced by a learned function (e.g., a model trained on real execution benchmarks on target hardware), the pipeline does not change — the rules remain formally verified, extraction remains correct, but the quality of generated code could improve without manual tuning effort.

This is not speculation: the cost model interface in AMO-Lean is already parameterized by a structure (`MatCostModel`) that is passed as an argument. Replacing it with a learned oracle requires changing the instantiation, not the architecture.

### Connection to Automated Theorem Proving

The connection between E-Graphs and automated theorem proving materializes in two directions.

**From E-Graphs to proofs.** lean-egg (Rossel, in development; paper accepted at POPL 2026) is a Lean 4 tactic that uses egg as a backend for equational reasoning. The tactic sends equalities to the E-Graph, saturates with the context's rules, and if it finds that both sides of a goal belong to the same e-class, generates a proof *witness* that the Lean kernel verifies. This maintains soundness: egg is an untrusted oracle, and Lean independently verifies each step. The work of Singher and Shachar (Easter Egg, FMCAD 2024) extends E-Graphs with "colors" for conditional reasoning with multiple simultaneous assumptions, building a purely E-Graph-based equational prover.

**From LLMs to rewrite rules.** Language models applied to formal proving (DeepSeek-Prover-V2, ReProver, LeanAgent, AlphaProof) operate by selecting tactics and premises to close goals in Lean. A concrete direction for AMO-Lean is to use these models to *discover* rewrite rules: given a DSL and a set of axioms, an LLM could propose candidate algebraic identities (e.g., "for Mersenne fields, $x^{2^{31}} = x \cdot (x-1)^{2^{31}-1}$"), and MetaM could attempt to prove them automatically with `ring` or `decide`. Rules that are proven are added to the E-Graph; those that are not are discarded. This would convert rewrite rule generation from a manual process to a semi-automatic proposal-and-verification loop.

One must be precise about the scope of this connection: current LLMs are not verifiers — they produce conjectures that may be false. The advantage of the AMO-Lean context is that a false conjecture has no consequence: if `ring` cannot close the goal, the rule simply does not compile. The cost of failure is a failed attempt, not a silent bug.


## Current Status and Limitations

It is important to be explicit about what is formally verified and what is not:

| Component | Status |
|---|---|
| Individual rewrite rules | 19/20 formally verified |
| Scalar rewriter correctness | Formally proven (`rewriteToFixpoint_sound`) |
| E-Graph compositional correctness | Valid informal argument; formalization in progress |
| Permutations (stride, bit-reversal) | Formally verified (with 1 documented axiom for tensor) |
| MatExpr → Σ-SPL → C pipeline | Correct by testing (1481+ tests); no formal proof of the translation |
| Proof Anchors | Traceability for auditing; not end-to-end mechanical verification |

AMO-Lean does not claim to be an end-to-end verified compiler at CompCert's level. What it offers is an optimizer where the algebraic transformations — the part most prone to subtle errors — are formally verified, with explicit traceability down to the emitted code.


## Conclusion

AMO-Lean demonstrates that it is viable to implement an equality saturation engine within a proof assistant with dependent types, without sacrificing either formal rigor or the ability to generate efficient code. SPIRAL's techniques for symbolic transform representation, combined with Mathlib's proof infrastructure and Lean 4's metaprogramming, produce a system where optimizing and verifying are the same activity.

The architecture is portable: the pattern of typed DSL + verified rules + E-Graph + cost model does not assume matrix structure. Recent advances in optimal extraction (OOPSLA 2024), learned cost models (ASPLOS 2025), and E-Graphs for automated theorem proving (POPL 2026) suggest that the techniques described here converge with active research lines in compilers, formal verification, and machine learning.

Source code is available at [repository link].


## References

- Willsey et al., *egg: Fast and Extensible Equality Saturation*, POPL 2021
- Franchetti et al., *SPIRAL: Code Generation for DSP Transforms*, Proceedings of the IEEE, 2005
- Zhang et al., *egglog: Better Together: Unifying Datalog and Equality Saturation*, PLDI 2023
- Goharshady et al., *Fast and Optimal Extraction for Sparse Equality Graphs*, OOPSLA 2024
- Cai et al., *SmoothE: Differentiable E-Graph Extraction*, ASPLOS 2025
- Yang et al., *TENSAT: Equality Saturation for Tensor Graph Superoptimization*, MLSys 2021
- Rossel et al., *Towards Pen-and-Paper-Style Equational Reasoning in ITPs by Equality Saturation*, POPL 2026
- Wang et al., *SPORES: Sum-Product Optimization via Relational Equality Saturation*, VLDB 2020
- Panchekha et al., *Herbie: Automatically Improving Floating Point Accuracy*, PLDI 2015
- Singher & Shachar, *Easter Egg: Equality Reasoning Based on E-Graphs with Multiple Assumptions*, FMCAD 2024
- Suciu et al., *Semantic Foundations of Equality Saturation*, ICDT 2025
- Yang et al., *LeanDojo: Theorem Proving with Retrieval-Augmented Language Models*, NeurIPS 2023
- Koehler et al., *Guided Equality Saturation*, POPL 2024
