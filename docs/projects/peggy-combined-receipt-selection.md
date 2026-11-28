# Ordered selection from two-rule Peggy receipts

The [combined worklist](peggy-combined-rule-worklist.md) and the
[numeric zero-sample adapter](peggy-worklist-ordered-selection.md)
now feed one ordered selection interface. `CheckedReplay` pairs a
driver-checked report with its reconstructed E-PEG. It is parameterized
by the driver's action type. The numeric and tagged checkers both use
`checkWith` to construct this object from their own driver.

`Cost.Bundle.Worklist.Combined.check` accepts the original table, the
designated opcodes, the visit budget and the tagged report. The caller
then supplies a pool typed against the returned endpoint. Its graph
and replayed partition determine admission through the existing
ordered extraction and SIMPLE reversion checks. The original
first-minimum policy applies to the caller's Nat-valued scorer.
`CheckedReplay.select_admitted` identifies the chosen member and its
successful admission. `CheckedReplay.select_min` bounds the score
against every eligible entry in that supplied pool. An empty or fully
rejected pool yields `none`.

## Receipt status and semantics

Both checked statuses permit selection. A `.fixed` receipt certifies
that the zero-sample and eval-scale matchers have no enabled action on
the endpoint. An `.exhausted` receipt used the full budget and leaves
enabled work. Neither statement depends on the candidate pool.

`Combined.CheckedReceipt.observe_eq` composes replay soundness with
the selected candidate's row and ordered root checks. It equates the
original and extracted Figure 11 tuples, including undefined results,
at every index. The premises are well-founded original demand,
valid original classes for the given model and input, a defined zero
opcode, a defined factor, and scaling that succeeds for every defined
right operand with that factor on the left. Replay supplies the
endpoint validity used by extraction. The receipt checks graph syntax
and classes. The opcode laws remain semantic premises.

`Combined.CheckedReceipt.observe_of_exec` also relates successful
SIMPLE tuple execution to the original observation under the shared
pass's Boolean negation law. The supported emitter handles direct
carried-slot eval roots of one parentless primitive loop.

## Regression

The fixture starts with 17 rows and visits `.zeroSample 13` and
`.evalScale 14`. At the fixed 20-row endpoint, [candidate generation](peggy-generated-candidate-pool.md)
binds the auxiliary eval indices through the two generated RHSs.
A one-step receipt passes as exhausted and is rejected if labelled fixed.

The minimum is confined to the supplied admitted pool. The adapter
covers these two matchers and the existing emitter fragment.

[Definitions](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Worklist/Combined/Defs.lean) ·
[Theorems](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Worklist/Combined/Thms.lean) ·
[Regression](../../tests/ssa/PeggySimpleValidation.lean)

```sh
lake build --wfail +Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Combined.Thms PeggySimpleValidationTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggySimpleValidation.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Combined.Thms
lake env leanchecker tests.ssa.PeggySimpleValidation
```
