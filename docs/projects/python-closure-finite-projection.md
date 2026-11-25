# Finite projection of Python closure store operations

The finite table records the existing heap's allocation frontier and bound
cell values. Its association list has unique addresses and every address
is below the frontier. Allocation reserves a range without adding rows.
Thus the same three cases survive readback: dangling addresses, allocated
unbound cells and bound cells. The projection keeps the original typed
frame, including its local slots, exact owned and captured cell identities,
and any aliases. It also retains closure values stored in cells.
[Runtime interface](../../Silmaril/Languages/Python/Core/Closure/Defs.lean)
· [Finite definitions](../../Silmaril/Languages/Python/Core/Closure/Finite/Defs.lean)

`HeapTable.exists_project_iff` characterizes the raw heap states in the
projection's image. Their backing maps are empty at or beyond the
allocation frontier. Starting from any finite witness, reserves and
writes preserve this condition. A raw heap with unused backing data
outside the frontier needs normalization before applying exact state
equality.

The step graph is selected by read, write or fresh-frame requests.
The label includes the entire request and response, and an unsuccessful
write keeps the source state. `Snapshot.execute_project` proves that
a finite operation returns the same response and the full projected
successor as the corresponding runtime operation. `step_iff` starts
from a fixed finite source. `execution_readback` threads each recovered
successor into the next step and preserves both the ordered action
list and the projection of every intermediate state.
[Projection theorems](../../Silmaril/Languages/Python/Core/Closure/Finite/Thms.lean)

The executable fixture creates a frame with a fresh owned address and
two captures of the same existing address. Writing through one capture
changes the read through the other. The fresh owned address stays
unbound, while reading or writing a dangling capture gives the
existing invalid-reference failure.
[Run fixtures](../../Silmaril/Languages/Python/Core/Closure/Finite/Examples.lean)

Checked dispatch also admits finite code rows keyed by the original
code keys. Their projections are exactly the runtime tables with
finite support. Dispatch uses the runtime resolver and preserves exact
lookup failures, parameter arity, capture validation and the saved
caller stack. The positional writes thread the finite heap in order.
Return and defined-error delivery retain the residual heap and recover
the exact saved caller, continuation and older stack.
[Dispatch theorems](../../Silmaril/Languages/Python/Core/Closure/Finite/Dispatch/Thms.lean)
· [Dispatch fixtures](../../Silmaril/Languages/Python/Core/Closure/Finite/Dispatch/Examples.lean)

These call-entry and delivery equations supply premises for whole
executor step correspondence. That theorem also has to cover operand
evaluation, body steps, receiving a result and storing it in the caller.
A serialized symbolic state additionally needs a codec that preserves
exact identities and response payloads.

```sh
make check CHECK_TARGETS='+Silmaril.Languages.Python.Core.Closure.Finite.Examples +Silmaril.Languages.Python.Core.Closure.Finite.Dispatch.Examples'
```
