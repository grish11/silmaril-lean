# Python Core comparison at the first unsupported operation

The dynamic comparison uses the same closed bodies, total relational entry
and full observations as the [static comparison](python-core-refinement.md).
It follows the existing Core steps. The `Focus` judgment selects the next
arithmetic operation according to the Core's left-to-right contexts. Its
uniqueness and existence proofs relate that selection to actual expression
steps. A state is marked exactly when the selected operation is disabled.
The transition into such a state survives and its outgoing steps are
disabled. Raising, finishing and literal returns require no arithmetic
operation. [Definitions](../../Silmaril/Languages/Python/Core/Refinement/Dynamic/Defs.lean)

For example, the addition-only profile can take the silent addition step in
`(1 + 2) // 3` and then reaches the marker for floor division. The profile
that supports only floor division safely evaluates `(1 // 0) // (2 + 5)`.
The left operand raises a defined `ZeroDivisionError` before the unsupported
addition would execute. The static comparison marks the whole body at entry
in both examples. [Regression examples](../../Silmaril/Languages/Python/Core/Refinement/Dynamic/Examples.lean)

Safety is equivalent to every reachable state in the unguarded Core
permitting its selected operation. On a safe input the sole maximal
observation is the exact Core exit. Adding features shrinks the dynamic
completed behavior sets, and the dynamic set is contained in the static
set at the same profile. A universal property on a safe smaller profile
lifts to every maximal observation of the stronger profile with a run
witness. Completion is still coarse per program. Once
a marker is reachable the observation set is the entire carrier, even
when a prefix executed before the marker.
[Theorems](../../Silmaril/Languages/Python/Core/Refinement/Dynamic/Thms.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Languages.Python.Core.Refinement.Dynamic.Examples +Silmaril.Languages.Python.Core.Refinement.Examples +Silmaril.Languages.Python.Core.Thms'
```
