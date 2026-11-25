# Typed MLIR `cf.switch` and `cf.assert`

Import `Silmaril.SSA.MLIR.CF.SwitchAssert` for the fragment and its public
execution theorems. The fragment uses the `CF.Basic` labels, typed edges,
frames and entry scope, together with the `Pure` variables, operand tuples
and total deterministic scalar operation interpretations.

## Switch and assertion

| Operation | Contract |
| --- | --- |
| `cf.switch` | A terminator that compares a signless integer flag against full-width bit patterns, takes the matching edge, and takes the mandatory default edge if there is no match. An empty case list is valid. |
| `cf.assert` | A nonterminator with one signless `i1` operand and a static string attribute. True continues in the same scope without binding a result. False aborts immediately. The message remains syntax metadata, and the pure observation records only the abort. |

`Switch` accepts every positive signless flag width from `i1` through
`i16777215` (`IntegerType::kMaxWidth`), including odd widths and widths greater
than 64. The inherited `Width` requires positivity, so zero-width types are
outside the fragment. A case constant has exactly the flag's width. Case bit
patterns must be distinct, so two source spellings for the same pattern (such
as `-1` and `255` at `i8`) would count as a duplicate. The Lean interface takes
already formed bitvectors. Each case pairs a constant with one successor edge.
The default and case edges each carry in-scope operands whose counts, types
and order match the target block arguments. Several distinct cases may target
the same block with different operands.

The dialect reference specifies the control behavior and operand rules. The
pinned LLVM sources specify the width cap, duplicate check, case value count
and type checks, and branch successor verification.

- [MLIR ControlFlow dialect](https://mlir.llvm.org/docs/Dialects/ControlFlowDialect/)
- [LLVM integer width limit](https://github.com/llvm/llvm-project/blob/fb29ca8163c3309160711e5a14eb46bc6d4fdad2/mlir/include/mlir/IR/BuiltinTypes.td#L705)
- [LLVM switch implementation](https://github.com/llvm/llvm-project/blob/fb29ca8163c3309160711e5a14eb46bc6d4fdad2/mlir/lib/Dialect/ControlFlow/IR/ControlFlowOps.cpp#L713-L776)
- [LLVM branch successor checks](https://github.com/llvm/llvm-project/blob/fb29ca8163c3309160711e5a14eb46bc6d4fdad2/mlir/lib/Interfaces/ControlFlowInterfaces.cpp#L77-L108)

## Execution and compatibility

`Cfg.run` uses one fuel unit per block, including that block's assertions and
terminator. It yields `some (.returned values)` at a return, `some .aborted` at
a failed assertion, and `none` if fuel is exhausted first. `Cfg.Diverges` means
that every finite budget yields `none`. `Cfg.run_add_of_some` proves that a
return or abort at a finite budget persists at every larger budget.

`Cfg.embed` inserts a Basic graph with the same labels, block parameters,
primitive operations and terminators. Basic terminators use their existing
interpreter. `Cfg.embed_run` proves equality at every fuel budget after mapping
Basic returns to `.returned`, and `Cfg.embed_diverges_iff` gives equivalence of
divergence. This also applies to the Basic output of the checked
[`scf.while` lowering](mlir-scf-while.md).

`Silmaril.SSA.MLIR.CF.SwitchAssert.Examples` checks that `cf.cond_br` can pass
different operand lists to the same successor, both in Basic and after
embedding. The module also checks two `i65` matches that differ at bit 64, a
default with a different argument profile, assertion success and failure,
divergence through a default-only `i1` switch, the width cap, and duplicate
bit patterns. Build the checks with
`lake build --wfail +Silmaril.SSA.MLIR.CF.SwitchAssert.Examples`.

The static checks reject a missing operand, an operand of the wrong width,
and an attempt to target the entry. Each `CF.Edge` shares one type list
between its label and its operands. Entry is a separate block field, while
edges take values from the successor label family. The runner starts at
`cfg.entry` and resolves each branch through `cfg.block label`.

The model describes typed scalar CFG fragments with explicit argument passing
and a separate entry. The return is a fragment boundary. Flattening allocated
nested CFGs is a separate stage. Textual parsing, printing, full MLIR
verification, general dominance, and runtime diagnostic behavior are outside
the model.
