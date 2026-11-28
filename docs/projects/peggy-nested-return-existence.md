# Finite return existence for checked parent/child PEG regions

The graph-local checker from #4403 supplies the typed parent and child
boundaries, primitive schedules, and the demand rank for Figure 11.
The converse uses the existing emitted nested SIMPLE statement.

`Accepted.FirstExits` records the outer first-pass count at the specified
index and a finite child pass at every strictly earlier outer iteration.
Each child pass query changes the outer coordinate to the current
activation. Its Figure 11 test samples reset the child coordinate to
zero and range over that child's own defined prefix. Child trip counts
may differ between activations. A zero outer pass has an empty
continuing prefix, so its child-pass condition is vacuous.

`Accepted.DefinedSlices` requires successful full-slice evaluation on
typed stores that realize the corresponding PEG scopes. It covers the
outer guard, child initialization on the current captures, child guard,
child update at continuing indices, and the complete outer commit from
the checked child evals and old outer captures. The total primitive law
discharges these slice obligations, and each finite child pass remains a
separate premise. The Boolean negation law connects the Figure 11 exit
tests to SIMPLE's continuation tests.

`Accepted.activate_of_firstExit` builds a child execution from its pass
and preserves the full commit entry store. `Accepted.trace_of_exits`
uses a fresh activation on each continuing outer step and constructs
an actual `WhileTrace` with the outer pass as its exact length.
`Accepted.returns_iff_exits` relates successful returns to the explicit
finite passes and the defined original eval. The forward direction
extracts the passes from the successful trace. Slice definedness is
used only to build the converse run.

The canonical-while regression derives the outer and child counts from
the actual Figure 11 countdown equations of the existing two-level
graph. It constructs the emitted trace for outer count two with child
counts two and one, and for outer count zero with no child pass needed.
The existing executable fixture also checks the accumulated result 4.

[Certificate definitions](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Region/Defs.lean) ·
[Finite return theorems](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Region/Thms.lean) ·
[Regression](../../tests/ssa/PEGCanonicalWhile.lean)
