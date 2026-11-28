# Inferring Peggy layouts from a checked primitive loop

`Cost.Bundle.Worklist.Generate.Infer.select` takes a checked replay receipt
and a Nat-valued scorer. It infers layouts from the replayed graph and uses
the replayed classes in the existing `Generate.Multi` wiring, legality,
reversion and selection pipeline. The generator provides the representative
rows and resolves the operand and root addresses.

Inference first runs `Region.Bundle.extract` on the endpoint's original
wiring. This requires the existing checked single parentless primitive loop,
with one θ per input slot and an ordered nonempty tuple of θ samples at a
common pass. If this seed check fails, inference produces no layouts.

The shared layout retains each address once, in first-occurrence order.
It takes the ordered result references, pass, negation and guard rows,
initializers, carried θ rows and next-state references, followed by the
binding rows of the checked guard and update schedules. Keeping every
carried update preserves the emitter's loop boundary even for slots that
are absent from the result tuple. Layout generation drops other table rows.
Materialization still sees the original ordered root tuple, including repeats.

For each nullary primitive bound by the update schedule and used by at
least two of its primitive operand occurrences, inference produces one
additional layout. It appends one copy of that source representative and
marks the second update use as variable, in schedule and operand order.
Uses are discovered by source address. The existing `Multi` checker uses
the replayed classes and types when binding the chosen port and all default
ports. Defaults use the first compatible address. The one varied port
can wire to the copied row or any other compatible row. A copied row can
therefore remain unused in some admitted candidates.

This space contains one shared layout and one copied layout per eligible
primitive, with `m` or `m + 1` rows for `m` retained addresses. It uses no
enumeration cap. `mem_uses` and `copySite_iff` characterize the discovered
use. `duplicateAt_spec` checks the representative list and the translated
typed port. `checkedSlice_has_copy` shows that each eligible primitive
contributes a layout, and `mem_layouts` and `mem_fromSlice` describe the
family. `Multi.mem_pool_iff` gives candidate coverage before admission.
`Infer.select_admitted` and `Infer.select_min` give checked selection and
a score bound over admitted materializations of the inferred family. The
selector keeps its first-minimum policy. Alternatives that require multiple
copies, copying a non-nullary computation, a different seed loop, or a
different choice of retained class representatives are outside this space.

Both checked replay statuses permit selection. For a numeric receipt,
`CheckedReceipt.observe_eq` applies to the selected value. It preserves
ordered Figure 11 observations at every index, including undefined results,
given well-founded original demand, valid original classes for the model
and input, and a zero opcode defined with value zero. `observe_of_exec` relates
successful execution of emitted SIMPLE to those observations under the
shared-pass Boolean negation law. The combined receipt analogues use
their existing factor and scaling premises.

The regression replays a zero-sample rewrite on the counting loop whose
live update reads the same constant twice. It infers layouts of 11 and 12
rows. Admitted materializations have primitive-row scores `4, 5, 5` and
update binding counts `2, 2, 3`. The third candidate actually executes two
constant bindings, and all three emit `[2, 17, 2]`. The selector chooses
cost 4. A seed whose outputs sample distinct pass addresses is rejected.

[Definitions](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Worklist/Generate/Infer/Defs.lean) ·
[Theorems](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Worklist/Generate/Infer/Thms.lean) ·
[Regression](../../tests/ssa/PeggySimpleValidation.lean)

```sh
lake build --wfail +Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer.Thms PeggySimpleValidationTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggySimpleValidation.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer.Thms
lake env leanchecker tests.ssa.PeggySimpleValidation
```
