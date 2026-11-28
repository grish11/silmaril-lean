# Ordered selection from checked zero-sample receipts

This adapter composes [bounded zero-sample replay](peggy-zero-sample-worklist.md)
with [ordered finite-pool selection](peggy-ordered-cost-selection.md).

First, `Cost.Bundle.Worklist.check` takes the original E-PEG, designated
zero opcode, budget and address receipt. It calls the existing worklist
checker and keeps the reconstructed endpoint with evidence of that
check. The caller then supplies a typed candidate list for that exact
endpoint graph. `CheckedReceipt.select` passes the endpoint's replayed
class partition to the existing ordered selector. The checker takes
no separately supplied final partition or graph.

Selection accepts both checked stop statuses. `CheckedReceipt.fixed`
requires a `.fixed` receipt and proves current-table coverage for this
rule. `CheckedReceipt.exhausted` requires `.exhausted` and proves the
visit budget was used with an enabled site remaining. The selector's
minimum, as stated by `CheckedReceipt.select_min`, ranges over admitted
entries in the supplied endpoint pool in either case. It retains the
same first-minimum tie policy and `none` for an all-rejected or empty
pool. Closure of the current table and minimum cost in that pool are
separate guarantees.

## Semantics

For the chosen interpretation and input, the original graph must have
well-founded demands and a valid source partition. The designated
nullary count instruction must return defined zero. Replay derives the
endpoint's well-founded demands and class validity. The selector uses
these derived premises to prove `CheckedReceipt.observe_eq`, exact
equality between the original and selected graphs' ordered Figure 11
observations, including bottom at every port and index.

`CheckedReceipt.observe_of_exec` carries a successful finite execution
of the emitted SIMPLE tuple back to the original Figure 11 observation
under the reverter's Boolean negation law. The checked fuel runner can
supply that execution via `Certificate.runFuel_exec`.
`CheckedReceipt.exec_iff_observe` adds the converse for defined
tuples when the guard and full simultaneous update are total on
defined stores. The emitter still handles direct carried-slot eval
roots at a shared pass in one parentless primitive loop.

## Regression

The ordered decrement fixture gains two auxiliary zero-sample redexes.
One visit revises the class partition and appends an initializer sample,
leaving the second site enabled. Two visits achieve current-table
closure. The candidate in each pool redirects an auxiliary eval index
to the first appended sample. The same wiring fails with singleton
classes, so admission exercises the replayed equality even though
the rewritten rows are outside the emitted guard and update slices.
The emitted tuple is `[2, 17, 2]` from `[5, 17]` with either
checked stop status. The exhausted prefix relabelled as fixed is rejected.

The pool is supplied for each reconstructed table. The adapter leaves
enumeration, global profitability and general saturation termination
outside the result.

[Definitions](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Worklist/Defs.lean) ·
[Theorems](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Worklist/Thms.lean) ·
[Regression](../../tests/ssa/PeggySimpleValidation.lean)

```sh
lake build --wfail +Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Thms PeggySimpleValidationTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggySimpleValidation.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Thms
lake env leanchecker tests.ssa.PeggySimpleValidation
```
