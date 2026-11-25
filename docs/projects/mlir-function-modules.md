# Typed MLIR function modules

Import `Silmaril.SSA.MLIR.Module.Thms` for the generic API or
`Silmaril.SSA.MLIR.Thms` to use it alongside the scalar lowerings.
`MLIR.Module Func` stores an ordered list of function declarations.
`MLIR.FuncOf Body` stores a name, input and output interfaces, and a body
whose type is `Body inputs outputs`. The client chooses both interface types.
For instance, the scalar fragment already has
`Arith.Block : List Width → Width → Type`. The isolated-region institution
uses ordered contexts at both ends of `Institution.Block`.

`MLIR.FuncModule Body` is definitionally `Module (FuncOf Body)`.
`FuncModule.toModule` and `FuncModule.ofModule` are identity conversions with
both inverse laws checked. `FuncModule.map` changes input and output
interfaces and applies a corresponding typed body translation to each
declaration. It preserves names and order. `FuncModule.toModule_map` and
`FuncModule.ofModule_map` identify that translation with `Module.map` of
`FuncOf.map` in both directions. All three maps have identity and composition
laws. `FuncModule.find?` returns the first declaration with a matching name,
including its interface and typed body, and commutes with translation.

The module is a collection of definitions. The API admits repeated names and
leaves symbol-table verification, call resolution and execution to clients.
The model uses original code and the existing Silmaril body APIs.
[MLIR Builtin module](https://mlir.llvm.org/docs/Dialects/Builtin/#builtinmodule-moduleop) ·
[MLIR Func dialect](https://mlir.llvm.org/docs/Dialects/Func/) ·
[Definitions](../../Silmaril/SSA/MLIR/Module/Defs.lean) ·
[Laws](../../Silmaril/SSA/MLIR/Module/Thms.lean)

The checked example translates a module from `Arith.Block` into isolated
`Institution.Block` expressions using the existing `Institution.Arith.translate`.
It checks name lookup across translation and the denotations of a straight-line
doubling function and a function that squares its input in an isolated region.
[Lean examples](../../Silmaril/SSA/MLIR/Module/Examples/Thms.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.MLIR.Module.Examples.Thms'
```
