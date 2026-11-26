# SCF and CF signature extension

## Checked fixed-sort extension

`Silmaril.MLIR.SCF.PrimitiveExtension` fixes a sort type and indexes operation symbols by the full
ordered MLIR institution profile, including the operand, result, region parameter and region yield
sorts. Maps are functions in each profile. The base can have isolated-region symbols. A fixed
family `P` supplies fresh primitives only at profiles with zero region slots. [Definitions](../../Silmaril/SSA/MLIR/SCF/ExtensionPrimitiveDefs.lean)

`extend P S` is a pointwise sum. Its inclusions are injective and their images are disjoint even
when the old and fresh symbols share a profile. `extendHomEquiv` gives the coproduct property
in this fixed-sort category. A map from the extension is uniquely determined by its
restrictions to `S` and `P.signature`, and every such pair gives a map. The endofunctor acts by the
given map on old symbols and the identity on fresh symbols. `extensionMonad` checks naturality,
both unit laws and associativity. Its unit is the old-symbol inclusion, and its multiplication
identifies corresponding primitives from the two successive fresh copies. Maps that change
sorts, replace symbols by terms, or require equations between symbols have different hypotheses. [Theorem interface](../../Silmaril/SSA/MLIR/SCF/ExtensionPrimitiveThms.lean)

The generic signature category permits sort maps and its disjoint sum tags sorts as well as
symbols. The fixed-sort extension shares the sorts across the base and fresh families, using the
same operation profiles and identity sort maps into the institution. [Generic signature category](https://github.com/hiloopai/silmaril-lean/pull/3166)

The inclusion gives an institution map, so `Term.denote_map` compares a renamed old term with the
original term in the reduct of a given extended model. Existence of such a model is a separate
condition. For example, `nullary_result_nonempty` shows that a nullary fresh primitive forces each
result carrier to be inhabited. An old signature with no symbols admits an empty carrier at that
sort, which rules out such an expansion of that model. The checked monad acts on symbol families
with the stated profile restrictions. Applying any analogous law to SCF or CF syntax would
require an account of their binders, terminators, successors, verifier constraints and effects. [Institution laws](../../Silmaril/SSA/MLIR/Institution/Thms.lean)

## Upstream operation matrix

The matrix uses the operation inventory in the SCF and CF references and the corresponding
TableGen definitions at LLVM revision `cc45e189bc99870d26d50c5e3a3d215068e74880`. The final
column records the initial scalar coverage and the boundary for each typed slice. [SCF reference](https://mlir.llvm.org/docs/Dialects/SCFDialect/) · [CF reference](https://mlir.llvm.org/docs/Dialects/ControlFlowDialect/) · [Pinned SCF definitions](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/SCF/IR/SCFOps.td) · [Pinned CF definitions](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/ControlFlow/IR/ControlFlowOps.td)

| Operation | Upstream contract | Boundary for a typed slice |
| --- | --- | --- |
| `scf.condition` | The `while` before-region terminator tests an `i1` and forwards a tuple to the after-region or to the loop results. | The merged scalar slice types the tuple against the after-region arguments and loop results. [#3167][while-cf] |
| `scf.execute_region` | Runs a region once, with no operands or entry arguments. It allows dominating captures and multiple blocks and exits. | Start with a single block and typed exit, then relate multiple blocks and captures to a typed CFG. |
| `scf.for` | Counts over a half-open range with positive step and optional loop-carried arguments and results. | The merged unsigned scalar slice checks positive step, no-wrap admission, and lowering to typed CF. [#3214](https://github.com/hiloopai/silmaril-lean/pull/3214) |
| `scf.forall` | Invokes a multidimensional body across virtual threads with shared tensor outputs and implicit synchronization. | Start with a specified shared-output update and disjoint slices. Add effect order and target mapping separately. |
| `scf.forall.in_parallel` | Terminates the `forall` body and groups the actions that contribute to the shared outputs. | Type actions against the enclosing destinations and specify how updates combine. |
| `scf.if` | Selects a then-region or optional else-region using an `i1`. A result-bearing `if` requires both arms to yield the result tuple. | The merged slice checks typed scalar arms, optional nested while loops, and their common result tuple under lowering to CF. [#3198](https://github.com/hiloopai/silmaril-lean/pull/3198) |
| `scf.index_switch` | Selects one region by an `index` selector and integer case labels, with a mandatory default region. | The merged 64-bit index slice checks case selection, the common yielded tuple and lowering to typed `cf.switch`. [#3223](https://github.com/hiloopai/silmaril-lean/pull/3223) |
| `scf.parallel` | Iterates a multidimensional half-open index space in unspecified order and supports parallel execution. Its single body block ends in `scf.reduce`. Data races have undefined behavior. | The merged pure model handles one mathematical natural-index dimension. The typed follow-on checks a statically admitted unsigned scalar induction value and passes the grouped result to an enclosing yield. [#3202][parallel-pure] · [Typed boundary](../../Silmaril/SSA/MLIR/SCF/ParallelYield/Thms.lean) |
| `scf.reduce` | Terminates the `parallel` body. Each operand and binary combiner region shares a type with the matching initial value and result. The order is unspecified. | The typed boundary indexes the contribution tuple, initial values and combiner regions by the same slot types. The result theorem ranges over the pure model's admitted orders and trees. [Typed boundary](../../Silmaril/SSA/MLIR/SCF/ParallelYield/Thms.lean) |
| `scf.reduce.return` | Exits a combiner region with one value of its reduction type. | The typed boundary checks a single returned value at the width of both combiner parameters. [Typed combiner interface](../../Silmaril/SSA/MLIR/SCF/ParallelYield/Defs.lean) |
| `scf.while` | Alternates two single-block regions. The initial operands go to the before-region, and the after-region sends the next inputs back. The before-region tuple and the loop results may have different types from the initial inputs. | The merged scalar slice checks separate region interfaces and proves that CF lowering preserves and reflects finite returns and divergence. [#3167][while-cf] |
| `scf.yield` | Returns a tuple at a structured region boundary. The parent decides the next destination, including the next iteration's before-region in `while`. | The merged while slice covers the after-region exit. The typed follow-on checks a one-shot enclosing yield and its agreement with a fragment return. [#3167][while-cf] · [Typed boundary](../../Silmaril/SSA/MLIR/SCF/ParallelYield/Thms.lean) |
| `cf.assert` | Tests an `i1` with a message attribute. True continues and false aborts execution. | The merged typed CF slice observes abort and keeps the message as syntax metadata. [#3184][switch-assert] |
| `cf.br` | Transfers control and operands to one successor block. | The merged scalar CFG types the operand tuple against the destination's block arguments. [#3167][while-cf] |
| `cf.cond_br` | Selects one of two successor edges using an `i1`. Each edge carries its own operands. Both can target the same block, and neither can target the entry block. | The merged scalar CFG types operand tuples per edge and puts the entry outside the destination labels. [#3167][while-cf] |
| `cf.switch` | Selects a successor by a signless integer selector and distinct case constants of the same type, with a mandatory default edge. | The merged typed CF slice checks distinct full-width case patterns and destination-typed operand tuples for every edge. [#3184][switch-assert] · [Pinned CF verifier](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Dialect/ControlFlow/IR/ControlFlowOps.cpp#L713) |

Natural subsets follow the interfaces in the matrix.

- Structured selection uses `if`, `index_switch` and their `yield`. A counted loop uses `for` and
  `yield`. The two-region loop uses `while`, `condition` and the after-region form of `yield`.
- Typed CFG transfer starts with `br` and `cond_br`, then adds `switch`. `execute_region` with
  internal CF branches and structured exits connects the CFG and region interfaces. `assert`
  introduces an abort effect independently of the choice of branch terminators.
- Parallel reduction uses `parallel`, `reduce` and `reduce.return`. `forall` and
  `forall.in_parallel` instead use a shared-output update interface and synchronization.

The scalar while-to-CF slice is on main at `8e0c832ace328d4c238f16fa84faa50c04f283d1`. Its
observations are a result tuple or divergence on total deterministic scalar operations. [While-to-CF lowering][while-cf]

[while-cf]: https://github.com/hiloopai/silmaril-lean/pull/3167
[parallel-pure]: https://github.com/hiloopai/silmaril-lean/pull/3202
[switch-assert]: https://github.com/hiloopai/silmaril-lean/pull/3184

## Checked typed parallel and structural yield boundary

`ParallelYield.Program` uses the merged one-dimensional pure reduction model at
`698b53c652a5db0e4afe2693ac17116d9e64b9e7`. It supplies the bounds as a mathematical index
space and requires the positive step and exit index to fit a fixed unsigned width.
`bounds_fit` and `indexValue_exact` check that the bounds and each induction value fit that width.
The body sees the induction value and the parent captures. Each combiner sees two values of
its slot type and the parent captures. Its `reduce.return` passes one value at the slot width.
The enclosing region receives the reduced tuple and the parent captures, and completes
with structural `scf.yield`. [Pure reduction model][parallel-pure] · [Typed definitions](../../Silmaril/SSA/MLIR/SCF/ParallelYield/Defs.lean)

`YieldRegion.asReturn_eval` proves agreement with a fragment return for any body in this
straight-line profile. The yield observation is the resulting tuple. A resumable effect would
have its own request, reply type and continuation. `Program.returns_iff_eq_denote` proves
that under slotwise associativity and commutativity the local reduction relation yields
exactly the reference result of the enclosing region. It inherits the initial-first and
shared-tree choices of the pure model. `Program.returns_iff_of_empty` shows that with zero
trips the enclosing region still runs on the initial tuple, with no algebraic hypotheses.
The checked examples use two widths, capture a parent value, and reorder the yielded tuple
after a local operation. [Theorems](../../Silmaril/SSA/MLIR/SCF/ParallelYield/Thms.lean) · [Lean examples](../../Silmaril/SSA/MLIR/SCF/ParallelYield/Examples.lean)

```sh
lake build --wfail +Silmaril.SSA.MLIR.SCF.ParallelYield.Examples
make check CHECK_TARGETS=+Silmaril.SSA.MLIR.SCF.ParallelYield.Examples
```

## Parallel and yield with LetIter

The scalar Arith bridge checks typed return observations in LetIter. The ranked-controller work
compiles finite ranked controllers to native LetIter. The cyclic nonrepresentability result shows
that a native visible loop in its mixed instruction model can have arbitrarily long visible
prefixes, whereas a written expression in that specific grammar has a uniform finite bound.
These results give a sequential baseline and a reason to track observable prefixes when extending
the language. Recent MLIR developments cover pure typed lowering and primitive-only RVSDG
translation. The concurrent constructs and comparisons below are open. [Arith bridge](../../Silmaril/SSA/MLIR/Arith/LetIter/Thms.lean) · [Ranked controller implementation and proof](https://github.com/hiloopai/silmaril-lean/commit/834bb6010d26f3bc5a30e616f7c044b3db97ca5f) · [Cyclic nonrepresentability](https://github.com/hiloopai/silmaril-lean/pull/3152) · [Pure MLIR observations](https://github.com/hiloopai/silmaril-lean/pull/3018) · [Regionless RVSDG translation](https://github.com/hiloopai/silmaril-lean/pull/3133)

The written mixed-expression normalization work covers loop-free expressions in a pure atomic
context with an atomic result. Its equality reflection is at the supplied source effect bound
under the stated primitive hypotheses. [Written LetIter normalization](https://github.com/hiloopai/silmaril-lean/pull/3163)

Structured yield returns control and a typed tuple to a parent region interface. A suspension yield
sends a value or request to a handler and leaves a continuation for possible resumption. A thread
yield is a scheduling event that may let a different thread step. An effect yield can be exposed
as a request and reply when that is the intended observation. These uses require distinct
constructors or explicit interpretations. In particular, the end of an upstream
`scf.parallel` body is a reduction terminator.

| Extension | LetIter AST research gap | MLIR-like AST research gap |
| --- | --- | --- |
| LetIter + Parallel | Add typed finite indexed bodies, captures and joins, with separately typed reduction operations. Show how the existing typing and sequential observations embed. | The checked typed pure slice covers one unsigned dimension and zero-trip initialization. Explicit shared outputs and synchronization belong to the `forall` slice. |
| LetIter + Yield | Add typed exits with explicit parent and payload interfaces for structured yield. A suspension extension needs a request, a reply type, a continuation and a choice of visible observations. | The checked one-shot structural boundary has a typed payload and explicit captures. A suspending or scheduling instruction needs its own operation and state, including a resume point if resumption is observable. |
| LetIter + Parallel + Yield | Type the owner of each yield across workers and the join. For resumable workers, define who resumes them and how suspension interacts with completion, divergence and cancellation if admitted. | The typed pure slice distinguishes per-trip contributions, combiner returns and the enclosing yield. A worker semantics still needs a scheduler, continuation state and a contract for effects around the join. |

**Operational stage.** The typed pure boundary fixes the scope of transferred payloads and
the finite iteration domain. A concurrent profile needs a worker and join transition system
with explicit rules for shared memory, races and synchronization. For suspension, specify
resume steps and which requests, replies, exits and finite prefixes are visible. State any
fairness hypothesis used in a liveness claim.

**Denotational stage.** In the pure model, the fixed-order sequential fold agrees with all
locally admitted orders and trees under the slotwise laws. Pure order-sensitive combiners
can expose multiple results. An effectful or suspending model needs observations of scheduling,
traces, abort and divergence and an adequacy or refinement theorem against the operational
semantics. Its equations depend on how parallel composition, sequencing and iteration interact.
