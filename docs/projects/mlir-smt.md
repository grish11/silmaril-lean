# Scoped MLIR SMT blocks

`Silmaril.MLIR.SMT` models a pure single-block slice after resolving SSA
operands, operation forms and types. Each operation reads earlier values and
binds one result. The top-level interface observes one selected SSA value.
A quantifier has one nested block, at least one typed block argument and one
`smt.yield` operand of type `!smt.bool`. Its result is a Boolean SSA value and can
be used anywhere the slice takes a Boolean operand.
[Definitions](../../Silmaril/SSA/MLIR/SMT/Defs.lean)

## Scopes and translation

- The source sorts `!smt.bool` and `!smt.int` map to `Uflia.SortCode.bool` and
  `Uflia.SortCode.int`. `Context.toSmt` maps a scope to a positional sorted context.
  The target signature has no uninterpreted symbols. Input SSA values are
  free term variables, given values by the typed input environment.
- Quantifier bodies can use their block arguments and values that dominate
  the enclosing quantifier operation. They have no reference to the
  quantifier's own result or to later definitions. Each argument adds a
  fresh slot in source order, with the last argument nearest. Lowering
  creates one target binder for each argument, outermost first. The
  continuation keeps the enclosing scope extended by the Boolean result.
- `Block.toSmt` returns an existing `Uflia.Quantified.Term` with the mapped
  context and result sort. A Boolean result also has the existing
  `Uflia.Quantified.Formula` type through `Block.toFormula`. Substituting a
  binding into its continuation uses `Term.instantiate`, which lifts
  substitutions under binders and shifts free references to avoid capture.

[Quantified SMT definitions](../../Silmaril/Logic/Smt/Uflia/Quantified/Defs.lean) ·
[Substitution](../../Silmaril/Logic/Smt/Uflia/Quantified/Substitution/Thms.lean)

`Block.eval_toSmt` proves agreement of direct, sequential SSA evaluation and
evaluation of the translated term for **every** typed input environment.
`Block.toFormula_holds_iff` gives the corresponding truth equivalence for
Boolean results. Both semantics quantify over the full standard domains
`Bool` and `Int`. They assign classical truth values to quantifiers. This
milestone includes no executable quantifier evaluator, finite approximation,
solver calls, solver answer validation, or SMT-LIB export.
[Theorem header](../../Silmaril/SSA/MLIR/SMT/Thms.lean)

`Examples.captured_not_holds` checks that a binding made outside two
quantifiers still refers to the original input, for either Boolean input.
An accidental substitution of either inner block argument for the captured
value would make the example true. `Examples.successor_holds` checks
`∀ n : Int, ∃ (m : Int) (flag : Bool), flag ∧ m = n + 1` over all integers.
Its inner body uses the outer bound value and an earlier SSA constant.
`Examples.wrong_sort_unavailable` checks that the sole integer in scope
cannot supply a Boolean operand.
[Checked examples](../../Silmaril/SSA/MLIR/SMT/Examples/Thms.lean)

## Upstream coverage

The inventory covers all 54 operations in the four SMT operation TableGen
files at llvm-project commit `cc45e189bc99870d26d50c5e3a3d215068e74880`.
The Lean and prose are original to Silmaril and use upstream definitions as
references. [SMT dialect documentation](https://mlir.llvm.org/docs/Dialects/SMT/) ·
[Pinned core operations][core] · [Pinned integer operations][ints] ·
[Pinned bitvector operations][bv] · [Pinned array operations][arrays] ·
[Pinned types][types] · [LLVM license][license]

| Upstream ops | Status and profile |
| --- | --- |
| `smt.constant`, `smt.not` | Checked for Boolean operands and results as applicable. |
| `smt.and`, `smt.or` | Checked at arity two. Larger variadic forms are deferred. |
| `smt.eq` | Checked for two operands of the same supported sort. Larger variadic forms are deferred. |
| `smt.ite` | Checked with a Boolean guard and two alternatives of the same supported sort. |
| `smt.int.constant`, `smt.int.add` | Checked for arbitrary integers, with binary addition. Larger variadic forms of addition are deferred. |
| `smt.forall`, `smt.exists` | Checked with one or more Bool/Int binders, including mixed lists, nesting and capture of dominating values. |
| `smt.yield` | Checked in the quantifier profile with exactly one Boolean operand. Solver and check terminators are deferred. |
| `smt.xor`, `smt.implies`, `smt.distinct` | Deferred Boolean and equality operations. |
| `smt.int.abs`, `smt.int.cmp`, `smt.int.div`, `smt.int.mod`, `smt.int.mul`, `smt.int.sub` | Deferred integer operations. Division and remainder need the SMT contract at zero. |
| `smt.bv.constant`, `smt.bv.add`, `smt.bv.and`, `smt.bv.ashr`, `smt.bv.cmp`, `smt.bv.concat`, `smt.bv.extract`, `smt.bv.lshr`, `smt.bv.mul`, `smt.bv.neg`, `smt.bv.not`, `smt.bv.or`, `smt.bv.repeat`, `smt.bv.sdiv`, `smt.bv.shl`, `smt.bv.smod`, `smt.bv.srem`, `smt.bv.udiv`, `smt.bv.urem`, `smt.bv.xor`, `smt.bv2int`, `smt.int2bv` | Deferred with bitvector sorts and conversions. |
| `smt.array.broadcast`, `smt.array.select`, `smt.array.store` | Deferred with array sorts. |
| `smt.declare_fun`, `smt.apply_func` | Deferred with function values and uninterpreted sorts. |
| `smt.assert`, `smt.check`, `smt.pop`, `smt.push`, `smt.reset`, `smt.set_logic`, `smt.solver` | Deferred solver state, effects and outcome regions. |

The profile also excludes zero-argument quantifiers (which upstream MLIR
admits), optional bound-variable name prefixes, pattern regions, the
`no_pattern` flag, and explicit weight metadata. References use positional
SSA identity. An MLIR text parser, a verifier for arbitrary dialect input and
integration with the generic SSA graph are outside this interface.
[Pinned region verifier][verifier] · [Upstream zero-argument examples][basic] ·
[Pinned exporter scope handling][exporter]

```sh
lake build --wfail +Silmaril.SSA.MLIR.SMT.Examples.Thms
make check CHECK_TARGETS=+Silmaril.SSA.MLIR.SMT.Examples.Thms
```

[core]: https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/SMT/IR/SMTOps.td
[ints]: https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/SMT/IR/SMTIntOps.td
[bv]: https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/SMT/IR/SMTBitVectorOps.td
[arrays]: https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/SMT/IR/SMTArrayOps.td
[types]: https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/SMT/IR/SMTTypes.td
[verifier]: https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Dialect/SMT/IR/SMTOps.cpp#L324
[basic]: https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/test/Dialect/SMT/basic.mlir#L153
[exporter]: https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Target/SMTLIB/ExportSMTLIB.cpp#L292
[license]: https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/llvm/LICENSE.TXT
