# Pure MLIR `scf.while` to CF

Import `Silmaril.SSA.MLIR.SCF.While` for the typed source, lowering, and
correctness statements. Import `Silmaril.SSA.MLIR.CF.Basic` for the target
alone. Both use the positive-width bitvectors, typed variables, and environments
from `Silmaril.SSA.MLIR.Arith.Defs`.

## Scope and lowering

`SCF.While Op Input Result` describes a parent block cut at one while
operation. `Input` contains the arguments and definitions already available at
that point. The initial operands select values from this context.
Each region and the parent continuation has a straight-line SSA body that binds
individual operation results and ends in a typed terminator.

| CFG block | Block arguments | Terminator |
| --- | --- | --- |
| Entry | Parent input | `cf.br` passes the initial state tuple to before. |
| Before | State tuple | `cf.cond_br` sends the `scf.condition` payload to after on true and to exit on false. |
| After | Payload tuple | `cf.br` passes the `scf.yield` state tuple back to before. |
| Exit | Payload tuple | The copied parent continuation returns the fragment result. |

The state and payload type lists may differ in length and element types. The
payload is both the after region's argument tuple and the result of the while
operation. The continuation can produce its own result type list. Region and
continuation arguments precede the captured parent values in their local
contexts. Locals stay inside the body that defines them. Any value used
by a successor outside the dominating parent input must travel as a branch
operand.

A `CF.Edge` uses a label indexed by its destination's argument types. Its
operands must match those types in order. A `CF.Cfg` provides a body for each
label. The entry is separate from that family and has no incoming edges. The
lowering specializes the family to three successor labels and copies each body
while replacing its terminator.

## Observable behavior

- `SCF.While.lower_run_succ` gives exact fuel correspondence. With CFG fuel
  `n + 1` the result is the source result at fuel `n / 2` (natural division).
  The entry consumes one CFG step. A source tick consumes two CFG steps, either
  before and after, or before and exit. Both evaluators return `none` at zero
  fuel.
- `SCF.While.lower_returns_iff` says a particular tuple is returned at some
  finite source budget exactly when it is returned at some finite target budget.
- `SCF.While.lower_diverges_iff` says that the source runs without returning at
  every finite budget exactly when the target does. Pure operation
  interpretations are total and deterministic, and all blocks have typed
  terminators, so an exhausted budget is the only reason an execution can lack
  a result.

The observation is the returned tuple or divergence. The fragment has one
while, with one block per region, a straight-line continuation, and a supplied
interpretation of regionless single-result primitives. Nested control flow,
effects, traps, textual MLIR, general CFG dominance, and a LetIter translation
are outside this contract. The return terminator is the fragment boundary.

`Silmaril.SSA.MLIR.SCF.While.Examples` checks a counting loop with distinct
state and payload arities, a captured input, a zero-iteration start, and the
first successful source and target budgets. It also proves divergence of an
always-true loop and transfers it to the lowered CFG. The examples are covered
by the existing `Silmaril.SSA.+` Lake glob.

- [LLVM MLIR SCF dialect and `scf.while`](https://mlir.llvm.org/docs/Dialects/SCFDialect/#scfwhile-scfwhileop)
- [LLVM MLIR Control Flow dialect](https://mlir.llvm.org/docs/Dialects/ControlFlowDialect/)
