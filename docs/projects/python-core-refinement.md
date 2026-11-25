# Python Core behavior refinement

The common input is a closed Python Core `Body`. The comparison model
always enters at `Body.start` through the relation
`initial body state := state = body.start`. Its observations are the full
Core instance of `RunObservation`, with `Completion` as both visible label
and terminal payload. The view is identity. An uncaught Python exception is
a defined exit with an `Except.error` payload.
[Comparison definitions](../../Silmaril/Languages/Python/Core/Refinement/Defs.lean)

The executable Core model checks admission before entry. A rejected body
has no initial state and no reachable UB in that model. The comparison
model instead supplies the start to the existing direct-state policy. An
unsupported start has reachable UB via zero steps, so the coarse completion
is the entire common observation set. If the profile supports the body,
the completed set is a singleton containing the structural evaluation
result with its one visible exit label. The proof classifies every maximal
run using the Core's progress, finite trace and termination theorems.
[Core admission](../../Silmaril/Languages/Python/Core/Defs.lean)
· [Behavior theorems](../../Silmaril/Languages/Python/Core/Refinement/Thms.lean)

Feature support checks the entire syntax tree. For example, a profile
that supports floor division but lacks addition marks
`(1 // 0) // (2 + 5)` at its initial state. The unrestricted Core reaches
`ZeroDivisionError` in the left operand before reducing the addition.
The comparison thus implements whole-program completion and can mark code
whose unsupported operation would never execute.
[Regression examples](../../Silmaril/Languages/Python/Core/Refinement/Examples.lean)

`behaviors_mono` proves that adding features shrinks the completed
behavior sets. `arithmetic_lt_addition` witnesses strictness using
`1 // 0`. The addition boundary admits a spurious successful return of
zero. With division enabled there is exactly one defined exception
observation. `lift_universal` applies when the smaller profile is UB-free
at the given body. It gives safety of the stronger profile, a maximal run
from its guaranteed entry, and the property for every maximal observation.
[Refinement and transfer](../../Silmaril/Languages/Python/Core/Refinement/Thms.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Languages.Python.Core.Refinement.Examples +Silmaril.Languages.Python.Core.Thms'
```
