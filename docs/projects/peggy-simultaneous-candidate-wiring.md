# Simultaneous operand choices after Peggy replay

`Cost.Bundle.Worklist.Generate.Multi.select` takes a checked worklist
receipt, a Nat-valued scorer, and a finite list of representative layouts
for the replayed table. Each layout supplies a representative row at each
target address and a list of typed row/operand positions to vary. Repeated
positions make the layout contribute no assignments. An empty position list
gives one assignment with all default bindings.

Each varied operand can use any target address whose representative has
the required sort and replayed class. The generator takes the full Cartesian
product of these choices. It uses the first compatible address for each
other operand and each ordered root. The layout fixes labels, sorts, and
the loop forest. Missing default bindings prevent materialization. The
existing single-operand `Generate` API remains available and shares the
materializer.

`Multi.mem_choices` characterizes this product in terms of the distinct
positions, exactly one assigned address per position, and per-address sort
and class compatibility. `Multi.resolve_assigned` shows that each assigned
address is used by the typed resolver for its port. `Multi.mem_pool_iff`
relates pool membership to this assignment predicate and successful
materialization. Enumeration is complete for these supplied layouts and
choices. It allocates the product and uses no enumeration fuel or candidate
cap. Its size can grow multiplicatively with the number of varied positions.

The existing checker validates rank, row and root class provenance, and
SIMPLE reversion, including use of a common pass. `Multi.select_admitted`
identifies the chosen pool member and its successful check. `Multi.select_min`
bounds its score against every admitted materialization of a valid assignment
in the supplied layouts. Ties keep the first admitted minimum by layout,
position, and address enumeration order. An empty or fully rejected pool
yields `none`. Layout synthesis and alternative bindings for unlisted ports
are outside this search space.

Both checked worklist stop statuses permit selection. The worklist's
`.fixed` report still concerns its two matchers, and `.exhausted` still
records the rewrite budget outcome. For a combined receipt, the selected
value has the existing `Bundle.Accepted` type. `Combined.CheckedReceipt.observe_eq`
preserves the ordered Figure 11 observations at every index, including
undefined results, given well-founded original demand, valid original
classes for the model and input, a defined zero opcode, a defined factor,
and scaling defined with this factor on the left for every defined right
operand. `observe_of_exec` relates successful execution of emitted SIMPLE to that same
source observation under the additional Boolean negation law for the
shared pass.

The regression checks an empty fixed combined receipt for the parentless
loop with two distinct returned values and a repeated result port. The
supplied layout places two same-class pass rows at addresses 8 and 9.
With both return edges varied, the four assignments have admission scores
`[some 8, none, none, some 5]`. The score is the sum of pass edge spans over
the ordered results. Either single substitution splits the pass and fails
SIMPLE admission. Changing both edges selects pass 9 and emits `[2, 17, 2]`.
Without the pass-class join, only the original wiring is generated. It
selects pass 8 at cost 8 and emits the same tuple. The earlier nonempty
combined receipt regression still exercises both rewrite tags.

[Definitions](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Worklist/Generate/Multi/Defs.lean) ·
[Theorems](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Worklist/Generate/Multi/Thms.lean) ·
[Regression](../../tests/ssa/PeggySimpleValidation.lean)

```sh
lake build --wfail +Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi.Thms PeggySimpleValidationTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggySimpleValidation.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi.Thms
lake env leanchecker tests.ssa.PeggySimpleValidation
```
