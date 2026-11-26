# Unsigned scalar MLIR `scf.for` to CF

Import `Silmaril.SSA.MLIR.SCF.For` for the typed source, executable admission,
lowering and correctness statements. The fragment describes one counted loop
in a parent block, with a single straight-line body and a continuation.
The body and continuation use the `Pure` SSA code and the same `scf.yield`
and fragment return types as the [while slice](mlir-scf-while.md).

## Profile and admission

This is the explicit `unsignedCmp` profile of `scf.for`. The lower bound,
upper bound, step and induction variable have the same positive-width signless
integer type, through MLIR's `i16777215` limit. The supplied bit patterns are
interpreted as unsigned for the loop control. The default signed comparison
and `index` types are outside this profile.

The mathematical trip count is the ceiling of `(upper - lower) / step`,
clamped to zero, with `step > 0`. `For.tripCount` computes it using natural
subtraction and ceiling division. The body receives the induction value
`lower + j * step` and the current carried tuple. `For.body_index_iff` proves
that the indices `j` before the trip count are exactly those whose induction
value lies below the exclusive upper bound. The body yields a tuple with the
same types as the initial operands. The continuation receives the last yielded
tuple, or the initial tuple if there were zero trips, followed by the parent
input. The induction variable stays local to the loop.

`For.Admitted` checks a positive step and representability of
`lower + tripCount * step`. That last value is used by the exit test, even when
it overshoots the upper bound. `For.inductionAt_fits` proves that the same
check bounds every body induction value and each update, including the final
one. `For.run` performs the admission check and yields `none` if it fails.
Lowering correctness applies to admitted inputs. Admission covers loop
control. The supplied regionless body and continuation primitives have their
own total deterministic interpretations.

- [MLIR SCF dialect and `scf.for`](https://mlir.llvm.org/docs/Dialects/SCFDialect/#scffor-scfforop)
- [Pinned LLVM loop contract](https://github.com/llvm/llvm-project/blob/fb29ca8163c3309160711e5a14eb46bc6d4fdad2/mlir/include/mlir/Dialect/SCF/IR/SCFOps.td#L157-L229)
- [Pinned LLVM integer width limit](https://github.com/llvm/llvm-project/blob/fb29ca8163c3309160711e5a14eb46bc6d4fdad2/mlir/include/mlir/IR/BuiltinTypes.td#L705)

## Lowering and exact execution

| CFG block | Action |
| --- | --- |
| Entry | Pass the lower bound and the initial carried tuple to the test. |
| Test | Compare induction and upper bound with `ult`. Pass induction and the carried tuple to the body on true. Pass only the carried tuple to the exit on false. |
| Body | Execute the copied body. After its yield, add the step and branch to the test with the new induction value and yielded tuple. |
| Exit | Execute the copied parent continuation on the final carried tuple. |

The increments use bitvector addition. The proof establishes that each
executed addition agrees with arbitrary-precision addition on admitted
inputs. This matches the role of `nuw` in LLVM's unsigned lowering. Explicit
argument passing uses `CF.Basic` typed edges and its restricted capture
discipline. [Pinned LLVM lowering](https://github.com/llvm/llvm-project/blob/fb29ca8163c3309160711e5a14eb46bc6d4fdad2/mlir/lib/Conversion/SCFToControlFlow/SCFToControlFlow.cpp#L330-L406)

`For.denote` executes exactly the mathematical number of bodies in order and
then the continuation. `For.lower_run` proves that on admitted inputs the
CFG returns this finite denotation at every fuel budget of at least
`2 * tripCount + 3`, and exhausts smaller budgets. `For.lower_run_at` compares
this first sufficient budget directly with `For.run`.

`Silmaril.SSA.MLIR.SCF.For.Examples` checks zero trips, three trips across the
signed bit boundary, a two-element carried tuple, a captured continuation
input, and the first successful CFG budgets. It also checks rejection of zero
step and overflow in the update after the only body. Run
`lake build --wfail +Silmaril.SSA.MLIR.SCF.For.Examples`.

This contract covers typed scalar fragments. Textual MLIR, nested CFG
flattening, parallel operations and full MLIR region verification are outside
this slice.
