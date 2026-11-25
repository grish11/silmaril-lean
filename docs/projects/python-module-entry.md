# Initialized Python module entry

The module Core runs an already lowered, straight-line module body against an
explicit global namespace. Import
`Silmaril.Languages.Python.Core.Module.Defs` for the executable interface and
`Silmaril.Languages.Python.Core.Module.Thms` for its correspondence proofs.
[Definitions](../../Silmaril/Languages/Python/Core/Module/Defs.lean)
· [Theorem header](../../Silmaril/Languages/Python/Core/Module/Thms.lean)

## Lowering interface

| Interface | Contract |
| --- | --- |
| `GlobalName` | The normalized string spelling supplied by source name resolution. Reads and writes use the same spelling. |
| `Globals.empty`, `Globals.ofBindings`, `Globals.lookup`, `Globals.bind` | Supply an empty store or seed it in order. A repeated seed takes the last value. Assignment replaces exactly the named binding. |
| `Expr.readGlobal`, `Stmt.assignGlobal`, `Stmt.assert` | Lower a global read, one-name assignment, or message-free assertion. The expression fragment has exact integers, booleans, integer addition and floor division, and numeric equality. |
| `Entry.start`, `Entry.run` | Start from the supplied store and statements. The runner returns the visible trace and a terminal state. |
| `State.advance`, `runPrefix` | Take a single labelled transition or a bounded prefix. The prefix returns its residual state even when still running. |
| `Observation` | Normal module completion or a defined exception, together with the residual namespace. |

A missing global read raises `NameError`. Addition, floor division and
equality evaluate operands from left to right. Booleans participate in numeric
operations as zero and one, and equality produces a boolean. Assignment
evaluates the right-hand side before updating the store. Assertions use
integer and boolean truth testing and raise `AssertionError` for a false
value. Errors in the condition propagate. The uncaught exception ends the
body, preserving earlier assignments in the observation. Bindings and final
completions emit labels. Successful assertions are silent.

## Proof and resolution boundary

`Globals.lookup_bind` and `Globals.lookup_bind_other` state readback and
preservation of other names. `Expr.eval_iff` and `State.advance_iff` connect
the executable evaluator and selector to independent rules.
`Entry.finishes_iff` identifies the full visible trace and exact terminal
observation with `Entry.run`. The step budget is one plus the number of
remaining statements. The rules prove determinism and absence of divergence
and UB for this profile.

The caller supplies module-level bindings and owns source resolution.
The store has one namespace with no implicit builtin fallback, implicit
module names, import resolution, or module loading. Admission belongs to
source lowering, including identifier normalization and rejecting any
operation that would require lookup beyond this namespace. The syntax covers
single-name assignment and message-free assertions with assertions enabled.
Imports, function and class definitions, calls, attribute access, container
values, patterns, implicit builtin lookup, assertion messages, and optimized
assertion removal are outside this profile. This increment supplies the
runtime target for expanded source intake. Corpus replay still depends on
that lowering.

The public specification baseline is Python 3.12.13. The Simple statements
HTML has SHA-256
`817344777aad7579f74f9260bb2f41e3c8368ae5dce0fe083c2a458af3504721`.
The Execution model HTML has SHA-256
`1928f7f11bbb47a652c55a292cb90bbd5c07224e0c6ddf019445ae653cd64102`.
The Expressions HTML has SHA-256
`d8c992b1815b59ba65aa9a0144bf2f0a24a3551cda8cbb06f5e76c5caec7d994`.
The Data model HTML has SHA-256
`c300d0904a1a03abd7752308eacffbdf7364d95d45f8e52d60076f38a21f763e`.
[Assignment](https://docs.python.org/release/3.12.13/reference/simple_stmts.html#assignment-statements)
· [Assertions](https://docs.python.org/release/3.12.13/reference/simple_stmts.html#the-assert-statement)
· [Name resolution](https://docs.python.org/release/3.12.13/reference/executionmodel.html#resolution-of-names)
· [Evaluation order](https://docs.python.org/release/3.12.13/reference/expressions.html#evaluation-order)
· [Integral types](https://docs.python.org/release/3.12.13/reference/datamodel.html#numbers-integral)

## Reproduce

```sh
make check CHECK_TARGETS='+Silmaril.Languages.Python.Core.Module.Thms'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/module-entry/Regression.lean
python3 -I tests/languages/python/module-entry/check_module_entry.py
```

The oracle compares completion classes and selected bindings for the public
fixtures with an explicit namespace and assertions enabled.
[Lean fixtures](../../tests/languages/python/module-entry/Regression.lean)
· [CPython replay](../../tests/languages/python/module-entry/check_module_entry.py)
