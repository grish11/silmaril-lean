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
column gives the boundary for a typed slice. [SCF reference](https://mlir.llvm.org/docs/Dialects/SCFDialect/) · [CF reference](https://mlir.llvm.org/docs/Dialects/ControlFlowDialect/) · [Pinned SCF definitions](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/SCF/IR/SCFOps.td) · [Pinned CF definitions](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/ControlFlow/IR/ControlFlowOps.td)

| Operation | Upstream contract | Boundary for a typed slice |
| --- | --- | --- |
| `scf.condition` | The `while` before-region terminator tests an `i1` and forwards a tuple to the after-region or to the loop results. | Tie the tuple to the after-region arguments and loop results. |
| `scf.execute_region` | Runs a region once, with no operands or entry arguments. It allows dominating captures and multiple blocks and exits. | Start with a single block and typed exit, then relate multiple blocks and captures to a typed CFG. |
| `scf.for` | Counts over a half-open range with positive step and optional loop-carried arguments and results. | Specify bound arithmetic, overflow and the empty range. Tie the body's yielded values to the carried tuple. |
| `scf.forall` | Invokes a multidimensional body across virtual threads with shared tensor outputs and implicit synchronization. | Start with a specified shared-output update and disjoint slices. Add effect order and target mapping separately. |
| `scf.forall.in_parallel` | Terminates the `forall` body and groups the actions that contribute to the shared outputs. | Type actions against the enclosing destinations and specify how updates combine. |
| `scf.if` | Selects a then-region or optional else-region using an `i1`. A result-bearing `if` requires both arms to yield the result tuple. | Type captures and a common result tuple, including the resultless case with no else-region. |
| `scf.index_switch` | Selects one region by an `index` selector and integer case labels, with a mandatory default region. | Type the labels and common yielded result tuple. Execute only the selected region. |
| `scf.parallel` | Iterates a multidimensional half-open index space in unspecified order and supports parallel execution. Its single body block ends in `scf.reduce`. Data races have undefined behavior. | Admit positive steps and the documented no-overflow condition. Separate independent pure contributions from shared effects. |
| `scf.reduce` | Terminates the `parallel` body. Each operand and binary combiner region shares a type with the matching initial value and result. The order is unspecified. | Match each contribution, combiner and result slot. Model the allowed orders before proving order independence. |
| `scf.reduce.return` | Exits a combiner region with one value of its reduction type. | Tie the returned type to the corresponding pair of combiner arguments. |
| `scf.while` | Alternates two single-block regions. The initial operands go to the before-region, and the after-region sends the next inputs back. The before-region tuple and the loop results may have different types from the initial inputs. | Keep the before and after interfaces distinct. Account for looping and divergence. |
| `scf.yield` | Returns a tuple at a structured region boundary. The parent decides the next destination, including the next iteration's before-region in `while`. | Type it against the parent-specific exit interface. |
| `cf.assert` | Tests an `i1` with a message attribute. True continues and false aborts execution. | Use a sequenced effect and explicit abort observation. Decide whether the message is observed. |
| `cf.br` | Transfers control and operands to one successor block. | Type the operand tuple against the successor's block arguments. |
| `cf.cond_br` | Selects one of two successor edges using an `i1`. Each edge carries its own operands, and both may target the same block. | Type operand tuples per edge, including when the destinations coincide. |
| `cf.switch` | Selects a successor by a signless integer selector and distinct case constants of the same type, with a mandatory default edge. | Check case uniqueness at the selector width and type every edge's operands against its destination. [Pinned CF verifier](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Dialect/ControlFlow/IR/ControlFlowOps.cpp#L713) |

Natural subsets follow the interfaces in the matrix.

- Structured selection uses `if`, `index_switch` and their `yield`. A counted loop uses `for` and
  `yield`. The two-region loop uses `while`, `condition` and the after-region form of `yield`.
- Typed CFG transfer starts with `br` and `cond_br`, then adds `switch`. `execute_region` with
  internal CF branches and structured exits connects the CFG and region interfaces. `assert`
  introduces an abort effect independently of the choice of branch terminators.
- Parallel reduction uses `parallel`, `reduce` and `reduce.return`. `forall` and
  `forall.in_parallel` instead use a shared-output update interface and synchronization.

The separate scalar while-to-CF slice checks finite return and divergence correspondence for
`while`, its region terminators and the typed `br` and `cond_br` targets. It supplies an initial
control-flow comparison for the matrix. [While-to-CF lowering](https://github.com/hiloopai/silmaril-lean/pull/3167)

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
| LetIter + Parallel | Add typed finite indexed bodies, captures and joins, with separately typed reduction operations. Show how the existing typing and sequential observations embed. | Start with typed `scf.parallel`-like iteration and reduction slots. Check bound admission and zero-trip initialization. Specify explicit shared outputs and synchronization as a separate `forall` slice. |
| LetIter + Yield | Add typed exits with explicit parent and payload interfaces for structured yield. A suspension extension needs a request, a reply type, a continuation and a choice of visible observations. | Check each structured exit against its parent or successor interface. A suspending or scheduling instruction needs its own operation and state, including a resume point if resumption is observable. |
| LetIter + Parallel + Yield | Type the owner of each yield across workers and the join. For resumable workers, define who resumes them and how suspension interacts with completion, divergence and cancellation if admitted. | Keep per-worker exits, reduction return and join results typed separately. For suspending workers, expose the scheduler and continuation state with explicit ordering of effects around a join. |

**Operational stage.** For structured exits, first prove scope and typing preservation for
transfers of payloads to parents. For parallel reduction, first give a finite pure semantics with
an explicit iteration domain, admissible enumeration and reduction orders, and initialization.
Compare a sequential reference fold with the relational outcomes for that profile. Add a worker
and join transition system for concurrency, with the treatment of shared memory, races and
synchronization stated as part of the profile. For suspension, specify resume steps and which
requests, replies, exits and finite prefixes are visible. State any fairness hypothesis used in
a liveness claim.

**Denotational stage.** A fixed-order sequential pure fold computes one result. A pure reduction
can collapse to a deterministic value once enumeration and permitted reassociation are proved
irrelevant, for example with a total associative and commutative combiner and each contribution
and initial value used exactly once. The empty iteration space returns the initial value. Without
such a proof, even pure reductions can expose multiple results. For effects or suspension,
choose observations of scheduling, traces, abort and divergence and prove an adequacy or
refinement theorem against the operational semantics. A trace or resumption model must account
for how parallel composition, sequencing and iteration interact before it can support their
combined equations.
