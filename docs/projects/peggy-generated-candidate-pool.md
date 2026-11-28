# Generating finite Peggy candidate pools after replay

`Cost.Bundle.Worklist.Generate.select` takes a `CheckedReplay`, a
Nat-valued scorer, and a list of `Skeleton`s for the replayed table.
It builds the pool from the table and its checked classes, then calls
the existing ordered selector. A skeleton specifies the representative
row at each target address and optionally one operand position to vary.
The representative supplies the row's sort and label. Its operand
addresses and the candidate's ordered root addresses are resolved by
generation. The loop forest is copied from the endpoint.

Each binding must match the required reference's sort and class. Ordinary
operands and roots use the first compatible target address in layout order.
Root positions follow the endpoint tuple, including repeated ports. At the
distinguished operand, generation visits every compatible address in layout
order. Without that operand there is one binding policy. A policy yields no
candidate if a required binding is unavailable. The existing admission
checker then checks cyclic demand rank, row and ordered-root class provenance,
and SIMPLE reversion for the supported parentless primitive loop.

`mem_choices_some` characterizes the varying addresses by sort and class.
`mem_pool_iff` characterizes the pool by the supplied layout, compatible
choice, and successful materialization. There is no candidate cap.
`select_admitted` proves a successful choice is a member and passed admission.
`select_min` gives a score bound over all admitted points in this finite space.
Ties keep the first admitted minimum in layout and choice order.
`select_none_iff` covers the empty and all-rejected cases. This leaves layout
discovery, simultaneous variation of several operands, and alternative
defaults outside the search space.

The generator accepts both checked worklist statuses. `.fixed` certifies
closure for the two replay matchers only. `.exhausted` permits selection
from the sound endpoint reached within the supplied rewrite budget.
For a combined receipt, `Combined.CheckedReceipt.observe_eq` applies
directly to the generated selection's accepted result. It equates the
original and selected ordered Figure 11 observations, including undefined
results, for every index. The premises are well-founded original demand,
valid original classes for the model and input, a defined zero opcode, a
defined factor, and scaling defined with that factor on the left for every
defined right operand. `Combined.CheckedReceipt.observe_of_exec` relates
successful emitted tuple execution to the original observations under the
additional shared-pass Boolean negation law.

The live regression checks `.zeroSample 13` and `.evalScale 14` on a 17-row
source. Two supplied layouts omit the old RHS representatives. The generated
wiring uses rows 17 and 19 of the fixed 20-row endpoint instead. Retaining the
zero-sample join alone leaves the pool empty because there is no compatible
binding for the eval-scale use. With both joins, materialization yields
primitive-row scores `[7, 7, 6]`. The live duplicate and shared candidates
both pass admission. Their update schedules have three and two bindings,
respectively. The selected cost-6 candidate emits `[2, 17, 2]` from `[8, 17]`.

[Definitions](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Worklist/Generate/Defs.lean) ·
[Theorems](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Worklist/Generate/Thms.lean) ·
[Regression](../../tests/ssa/PeggySimpleValidation.lean)

```sh
lake build --wfail +Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Thms PeggySimpleValidationTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggySimpleValidation.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Thms
lake env leanchecker tests.ssa.PeggySimpleValidation
```
