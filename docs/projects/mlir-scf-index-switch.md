# Lowering a 64-bit MLIR `scf.index_switch`

Import `Silmaril.SSA.MLIR.SCF.IndexSwitch.Thms` for the structured syntax,
evaluator, lowering, and correctness theorems. The target is the
[typed CF fragment](mlir-cf-switch-assert.md) from #3184.

## Upstream boundary

At llvm-project commit `fb29ca8163c3309160711e5a14eb46bc6d4fdad2`,
`scf.index_switch` takes an `index`, a mandatory default region, and any
number of case regions with signed 64-bit case attributes. Its verifier checks
one region per case value, uniqueness, and a yield of the declared result
types in order from every single-block region. Upstream lowering splits the
parent block, casts the flag to signless `i64`, and passes each yield to the
continuation using `cf.br`. The `cf.switch` verifier checks the case element
type, count, and uniqueness, and the branch interface checks successor
operand counts and types. [SCF operation][scf-op] · [SCF verifier][scf-verify] ·
[SCF-to-CF conversion][lower] · [LLVM regression][llvm-test] ·
[CF operation][cf-op] · [CF verifier][cf-verify] · [Branch interface][edges]

This model chooses a layout with 64-bit `index`. The input operand designated
by `Program.selector` has `indexWidth` in the shared width-indexed SSA
representation. It denotes the source index and is also the target flag:
the upstream `arith.index_cast` to signless `i64` preserves every bit at this
layout, so the model erases it. Other index layouts are outside the model.
[Builtin index type][index] · [Index cast][cast]

`CaseValue` stores the bits of an already decoded `int64_t` attribute.
Every 64-bit pattern has a unique signed interpretation via `BitVec.toInt`.
Source dispatch compares those signed interpretations, while target dispatch
compares the original bit patterns. The proof uses injectivity of
`BitVec.toInt` to equate the two tests. The case list pairs each key with its
region, and `Nodup` on the patterns checks the upstream uniqueness condition
and supplies the target uniqueness proof directly. No narrowing conversion
can introduce an alias between distinct cases.

## Typed fragment and observations

The model gives each case and the default its own straight-line body of
typed, total, deterministic scalar operations. The regions take no block
arguments and can reference the dominating input. Every `scf.yield` carries
the same typed result tuple, which may be empty. The parent continuation can
use that tuple and the original input. Its return is the observation at the
fragment boundary. Upstream permits other MLIR value types, effects, and
nested operations. This fragment models scalar bitvector values and pure
straight-line code, with operation interpretations supplied by the caller.
MLIR type and layout well-formedness beyond the encoded width and scope
constraints is assumed when relating an actual upstream program to this
fragment. Parsing and whole-module conversion are outside its scope.

`Program.lower` emits one flat CFG with a `cf.switch` entry, a label for each
case and the default, and one shared join. Switch edges pass no arguments.
Each arm ends in a typed `cf.br` whose operands become the join arguments.
The join executes the parent continuation. Both evaluations spend one tick
each on dispatch, the selected arm, and the continuation.

- `Program.lower_run` equates the target outcome with the structured result
  at every fuel budget. Budgets 0–2 exhaust, and every budget of at least 3
  returns the same tuple.
- `Program.lower_returns_iff` preserves and reflects each returned tuple at
  the same finite budget.
- `Program.lower_ne_aborted` rules out abort at any budget.
  `Program.lower_not_diverges` rules out divergence by the return at budget 3.

`Silmaril.SSA.MLIR.SCF.IndexSwitch.Examples` checks separate cases for
`0`, `2^32`, and `-2^63`, a `2^33` selector that reaches the default, a
two-value yield consumed by the continuation, insufficient fuel, a
result-bearing zero-case switch, an empty yield, and rejection of a repeated
bit pattern.
Run `lake build --wfail +Silmaril.SSA.MLIR.SCF.IndexSwitch.Examples`.

[scf-op]: https://github.com/llvm/llvm-project/blob/fb29ca8163c3309160711e5a14eb46bc6d4fdad2/mlir/include/mlir/Dialect/SCF/IR/SCFOps.td#L1174-L1264
[scf-verify]: https://github.com/llvm/llvm-project/blob/fb29ca8163c3309160711e5a14eb46bc6d4fdad2/mlir/lib/Dialect/SCF/IR/SCF.cpp#L4011-L4106
[lower]: https://github.com/llvm/llvm-project/blob/fb29ca8163c3309160711e5a14eb46bc6d4fdad2/mlir/lib/Conversion/SCFToControlFlow/SCFToControlFlow.cpp#L674-L732
[llvm-test]: https://github.com/llvm/llvm-project/blob/fb29ca8163c3309160711e5a14eb46bc6d4fdad2/mlir/test/Conversion/SCFToControlFlow/convert-to-cfg.mlir#L660-L716
[cf-op]: https://github.com/llvm/llvm-project/blob/fb29ca8163c3309160711e5a14eb46bc6d4fdad2/mlir/include/mlir/Dialect/ControlFlow/IR/ControlFlowOps.td#L242-L320
[cf-verify]: https://github.com/llvm/llvm-project/blob/fb29ca8163c3309160711e5a14eb46bc6d4fdad2/mlir/lib/Dialect/ControlFlow/IR/ControlFlowOps.cpp#L713-L776
[edges]: https://github.com/llvm/llvm-project/blob/fb29ca8163c3309160711e5a14eb46bc6d4fdad2/mlir/lib/Interfaces/ControlFlowInterfaces.cpp#L77-L108
[index]: https://github.com/llvm/llvm-project/blob/fb29ca8163c3309160711e5a14eb46bc6d4fdad2/mlir/include/mlir/IR/BuiltinTypes.td#L612-L634
[cast]: https://github.com/llvm/llvm-project/blob/fb29ca8163c3309160711e5a14eb46bc6d4fdad2/mlir/include/mlir/Dialect/Arith/IR/ArithOps.td#L1845-L1860
