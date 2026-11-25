# Python closure compiler runtime interface

The compiler-facing environment lives in
`Silmaril.Languages.Python.Core.Closure`. The runtime represents exact
integers and functions with a code-table key and ordered captured cell
identities. A `CodeRef` records its expected frame layout. The compiler
supplies the layout and the mapping from source bindings to bounded
slots. [Lean definitions](../../Silmaril/Languages/Python/Core/Closure/Defs.lean)

## Slots and captures

| Interface | Compiler use |
| --- | --- |
| `Layout`, `Slot layout` | Count direct locals, owned cells and incoming captures. Each slot is a `Fin` of the corresponding count. |
| `ParameterSlot layout`, `Parameters layout` | Supply direct-local or owned-cell parameter destinations in declaration order, with no repeated destination. |
| `Frame.fresh`, `Function.freshFrame` | Initialize unbound direct locals and allocate fresh owned cells. Incoming captures keep their supplied identities. |
| `Frame.read`, `Frame.write` | Load or update a slot. Cell updates return the residual shared heap and preserve the frame's slot-to-cell mapping. |
| `Frame.closure`, `Function.ofCaptureList` | Create a closure in child capture order using a bounded parent-slot map or an ordered list with its length proof. |

The source layout checker can use `Frame.owned` and `Frame.captures` for
its owned and forwarded lookups. Each has type `Fin count → CellId`.
The list interface can consume the resulting capture list and its length
proof directly. Source resolution establishes which indices correspond to
which bindings. The runtime preserves addresses and their order independently.
[Source layout candidate #2253](https://github.com/hiloopai/silmaril-lean/pull/2253)

Theorems establish freshness and disjointness of owned allocations, preservation
of existing cells during allocation and writes, ordered capture lookup and
readback through an alias. An allocated unbound cell differs from an invalid
address. Incoming unbound reads correspond to Python `NameError`. Unbound
direct local and owned-cell reads correspond to `UnboundLocalError`.
[Theorems](../../Silmaril/Languages/Python/Core/Closure/Thms.lean)
· [Regression](../../tests/languages/python/closure-runtime/Regression.lean)

## Fixed positional calls and saved-caller delivery

`Core.Closure.Call.bindPositional` binds argument values in order to the
distinct `Parameters.slots`. Its success is equivalent to the arity test and
the ordered `Writes` relation. Arity mismatch is a defined error with no
committed write. `Call.enter` accepts a function and its positional layout,
checks the incoming cell identities against the original heap, binds the
arguments in a fresh frame and pushes the saved caller. The binding proof
preserves the owned and incoming cell identities. `Call.enter_complete`
guarantees entry when arity matches and the captured addresses are allocated,
including captures that are still unbound. `Call.enter_read` proves that each
argument is readable at its compiler-assigned local or owned-cell slot.
`Call.enter_preserves_cell` covers every previously allocated caller cell,
including any incoming capture, before callee execution begins.
[Call definitions](../../Silmaril/Languages/Python/Core/Closure/Call/Defs.lean)

A `Call.Saved` stores the caller's layout, frame and typed continuation.
`Call.finish` hands a returned value or defined error to that continuation
with the callee's residual heap. It restores the saved frame and older stack
exactly. The saved frame provides the direct locals and cell identities.
The residual heap provides the latest values of shared cells. An empty stack
emits a terminal result. Invalid cell addresses use `Failure`, outside the
defined outcomes in `Result`.
[Call theorems](../../Silmaril/Languages/Python/Core/Closure/Call/Thms.lean)
· [Binding and delivery regression](../../tests/languages/python/closure-runtime/Call.lean)

## Checked code-table dispatch

`Core.Closure.Dispatch.CodeTable` indexes entries by the numeric code key.
Each entry associates a frame layout with the body and positional parameters
for that layout. `Dispatch.resolve` checks the closure's expected layout and
`Dispatch.dispatch` binds already-evaluated positional values. The result
contains the exact typed body and the entered frame and stack required to
start executing it. `Dispatch.dispatch_iff` characterizes successful
dispatch through table membership, capture liveness and the ordered
`Call.Writes` relation.

Missing code, mismatched layouts and dangling cells indicate invalid runtime
references. An integer callee and a positional arity mismatch produce defined
Python errors. The definition's body family is a parameter of dispatch.
[Dispatch definitions](../../Silmaril/Languages/Python/Core/Closure/Dispatch/Defs.lean)
· [Dispatch regression](../../tests/languages/python/closure-runtime/Dispatch.lean)

## Fixed positional body execution

`Core.Closure.Executor` instantiates the code table with layout-indexed bodies.
The supported instructions store a value, call with positional arguments and
store the result, or return. Operands are values, bounded slot reads and
closure creation with a bounded capture map. The callee is evaluated before
its arguments, which are evaluated left to right before dispatch.

The executor shares the frame and heap APIs with the compiler. Call entry
starts the selected body with its initialized frame. Return or an uncaught
defined error reaches a receiving state with the exact saved caller,
continuation and older stack, and the callee's residual heap. A successful
return writes the caller's result slot. An error unwinds to the next
continuation without that write. Invalid runtime references stop in a
separate fault state. The trace records entry, delivery, completion and
fault labels. Primitive reads and writes use the existing frame operations.

`Executor.step_iff` proves both directions of correspondence between the
selector and the rules, including argument evaluation and dispatch
rejection. `Executor.run_path` relates each fuel-bounded execution to a
labelled path with the same residual state. Fuel counts transitions.
The code table may contain recursive calls. The fragment has a finite
instruction sequence per body and guarantees termination of each selector
invocation and bounded prefix. It makes no global termination claim.

This syntax covers explicit returns and uncaught errors. Branches, loops,
arithmetic operands, globals, keyword and variadic arguments, defaults,
exception handlers, cleanup, generators and host operations require
additional runtime profiles.
[Executor definitions](../../Silmaril/Languages/Python/Core/Closure/Executor/Defs.lean)
· [Executor theorems](../../Silmaril/Languages/Python/Core/Closure/Executor/Thms.lean)
· [Executor regression](../../tests/languages/python/closure-runtime/Executor.lean)

The public baseline is the Python 3.12.13 language reference. The Data model
HTML has SHA-256 `c300d0904a1a03abd7752308eacffbdf7364d95d45f8e52d60076f38a21f763e`.
The Execution model HTML has SHA-256
`1928f7f11bbb47a652c55a292cb90bbd5c07224e0c6ddf019445ae653cd64102`.
The Expressions HTML has SHA-256
`d8c992b1815b59ba65aa9a0144bf2f0a24a3551cda8cbb06f5e76c5caec7d994`.
[Closure cells](https://docs.python.org/release/3.12.13/reference/datamodel.html#function.__closure__)
· [Name resolution](https://docs.python.org/release/3.12.13/reference/executionmodel.html#resolution-of-names)
· [Calls](https://docs.python.org/release/3.12.13/reference/expressions.html#calls)

```sh
lake build --wfail +Silmaril.Languages.Python.Core.Closure.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/closure-runtime/Regression.lean
lake build --wfail +Silmaril.Languages.Python.Core.Closure.Call.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/closure-runtime/Call.lean
lake build --wfail +Silmaril.Languages.Python.Core.Closure.Dispatch.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/closure-runtime/Dispatch.lean
lake build --wfail +Silmaril.Languages.Python.Core.Closure.Executor.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/closure-runtime/Executor.lean
```
