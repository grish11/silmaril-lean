# Typed MLIR function modules

Import `Silmaril.SSA.MLIR.Module.Thms` for the generic API or
`Silmaril.SSA.MLIR.Thms` to use it alongside the scalar lowerings.
`MLIR.Module Func` stores function declarations in order under unique symbol
names. `MLIR.FuncOf Body` stores input and output interfaces and a body whose
type is `Body inputs outputs`. The body representation determines scope and
terminators. For instance, the scalar fragment already has
`Arith.Block : List Width → Width → Type`. The isolated-region institution
uses ordered contexts at both ends of `Institution.Block`.

`MLIR.FuncModule Body` is definitionally `Module (FuncOf Body)`.
`FuncModule.toModule` and `FuncModule.ofModule` are identity conversions with
both inverse laws checked. `FuncModule.map` changes input and output
interfaces and applies a corresponding typed body translation to each
declaration. It preserves names and order. `FuncModule.toModule_map` and
`FuncModule.ofModule_map` identify that translation with `Module.map` of
`FuncOf.map` in both directions. All three maps have identity and composition
laws. `Module.find?` looks up a function by its symbol and commutes with
translation. In the typed view, the result includes the interface and body.

This profile covers collections of definitions. Call resolution and execution
belong to the client. The model uses original code and the existing Silmaril
body APIs.
[MLIR Builtin module](https://mlir.llvm.org/docs/Dialects/Builtin/#builtinmodule-moduleop) ·
[MLIR Func dialect](https://mlir.llvm.org/docs/Dialects/Func/) ·
[Definitions](../../Silmaril/SSA/MLIR/Module/Defs.lean) ·
[Laws](../../Silmaril/SSA/MLIR/Module/Thms.lean)

The checked example translates a module from `Arith.Block` into isolated
`Institution.Block` expressions using the existing `Institution.Arith.translate`.
It checks that duplicate symbols are excluded, checks lookup across translation,
and computes the denotations of a straight-line doubling function and a function
that squares its input in an isolated region. The tuples in the institution
example are pure results of its body representation.
[Lean examples](../../Silmaril/SSA/MLIR/Module/Examples/Thms.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.MLIR.Module.Examples.Thms'
```
