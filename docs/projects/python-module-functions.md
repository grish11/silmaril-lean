# Module functions and positional calls

Import `Silmaril.Languages.Python.Core.Module.Functions.Defs` for publication
and invocation, and the matching `Thms` header for correspondence. The
module uses the existing closure executor and its layout-indexed code table.
[Definitions](../../Silmaril/Languages/Python/Core/Module/Functions/Defs.lean)
· [Theorem header](../../Silmaril/Languages/Python/Core/Module/Functions/Thms.lean)

## Lowering interface

| Operation | Contract |
| --- | --- |
| `Session` | Supply the initialized global lookup and shared heap. The lookup maps normalized names to exact integers, booleans, or functions. |
| `Session.bindGlobal` | Publish an already evaluated value at a name. All other bindings and the heap are preserved. |
| `TopFunction`, `Session.publish` | Supply a code reference with no incoming cells. The executor checks code presence and layout, then binds the function in statement order. The body is entered at call time. |
| `Session.prepareCall` | Lower the callee and positional operands as literals or global reads. Select a result destination of discard, named binding, or truth assertion. |
| `Invocation.runPrefix`, `Invocation.finish?` | Execute a bounded labelled path. A terminal call yields its result or error and the exact residual namespace and heap. A live call can continue from the returned invocation. |
| `Executor.Operand.readGlobal`, `Executor.advanceIn` | Lower a global read inside a function. The executor reads the current module namespace supplied by the invocation, including in nested calls. |

The scalar module interface can seed a session by mapping each
`Core.Module.Globals.lookup` value to the corresponding `Core.Closure.Value.int`
or `Core.Closure.Value.bool`. Subsequent scalar assignments and function
publications update the same session lookup. A published function retains its
code reference and cell identities. A binding changed between publication and
invocation therefore changes what a function sees. A missing name raises
`NameError`, including inside a callee.

The executor evaluates the callable and then the operands left to right.
An argument error can precede a non-callable error. Wrong arity and
non-callable values are defined errors. A successful call assigns the
result only after the callee returns. A defined error skips that assignment
and preserves the previous binding. Truth assertion consumes the returned
integer, boolean, or function value after the call and reports
`AssertionError` when false. A runtime fault such as a malformed code
reference has its own completion class. The trace is the executor's trace,
including delivery to the internal caller that holds the result slot.
The internal caller allocates no heap cells.

`Session.publish_iff` requires an exact layout-matched table entry and
identifies the namespace update. `Executor.stepIn_iff` proves both directions
between the executor selector and the rules with global lookup.
`Invocation.run_path` witnesses the exact labelled prefix, and
`Invocation.finish_iff` relates terminal delivery to independent rules.
These rules retain the executor's residual heap even after an error.

## Scope

The caller sequences lowered module operations. This slice covers
undecorated function publication, global reads, and fixed positional calls.
Top-level operands are literals or reads. It supports an assigned call, a
discarded call, or a direct truth assertion on the returned value. Source
scope, whole-module lowering, imports and builtin lookup are separate
contracts. Defaults, decorators, keyword and variadic calls, writes to
module globals from function bodies, class bodies and handlers are outside
this slice. Each invocation is synchronous with a stable namespace during
its bounded prefix. Recursion is permitted and the bound supplies no
global termination theorem.

The public spec baseline is Python 3.12.13. The Compound statements HTML has
SHA-256 `a52088b56170cf5ddafcb39451fc77d30b99940a07b5af0ce47f86c28364647f`.
The Expressions HTML has SHA-256
`d8c992b1815b59ba65aa9a0144bf2f0a24a3551cda8cbb06f5e76c5caec7d994`.
[Function definitions](https://docs.python.org/release/3.12.13/reference/compound_stmts.html#function-definitions)
· [Calls](https://docs.python.org/release/3.12.13/reference/expressions.html#calls)

```sh
make check CHECK_TARGETS='+Silmaril.Languages.Python.Core.Module.Functions.Thms'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/closure-runtime/ModuleFunctions.lean
```
