# Finite projection of Python local slots

The finite presentation uses the existing typed `Locals.Store` and
local-step relation.
A Mathlib association list records the bindings of the
`Fin slots → Option Int` store. Entry keys are distinct and the key type
bounds every slot. `rowsOf` enumerates all slots. Looking up those rows
recovers the complete store. Encoding a state keeps its control, result
or error and projects back to the same semantic state.
[Typed locals](../../Silmaril/Languages/Python/Core/Locals/Defs.lean)
· [Finite definitions](../../Silmaril/Languages/Python/Core/Locals/Finite/Defs.lean)

The finite step uses the existing expression selector over the projected
lookup. A write updates the finite rows and emits the original write
event. `Presentation.advance_view` commutes with the existing selector,
including absent reads and exits. `step_iff` starts from a specified
finite source and gives an exact finite successor witness for each
actual local step. It preserves the action, including silent steps, and
the entire projected successor.
[Projection theorems](../../Silmaril/Languages/Python/Core/Locals/Finite/Thms.lean)

`execution_readback` threads those finite successors through a given
CSLib execution. It keeps the exact original action list and projects
the full list of intermediate states. Only a finished frame has a
terminal completion. Returning an integer and raising an uncaught
`UnboundLocalError` are two defined results; the intermediate raising
state has no terminal completion. The fixtures prove write, read and
return through one execution, and separately lift the unbound-local
execution and its terminal exception.
[Run fixtures](../../Silmaril/Languages/Python/Core/Locals/Finite/Examples.lean)

For runtime cells and heaps, the same
[readback criterion](operational-finite-projection.md) requires explicit
layout invariants and exact correspondence for the selected allocation
policy. If a symbolic codec records the finite rows, its decoder must
also recover the representation required by each incoming action.

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Core.Locals.Finite.Examples
```
