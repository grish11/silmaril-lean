# A pure Sea of Nodes loop in typed MLIR CF

Import `Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms`. The input is an
actual `Loop.Graph` with word-valued captures, carried values, and one word
result. `Bank.lower` emits a typed bank and `lower` is its single-latch
specialization. The ordered producer tables use scalar constants, flag-free
addition, subtraction and multiplication, and signed and unsigned less-than.
The lowering reuses the scalar producer-name table. A comparison produces an
`i1` consumed by `cf.cond_br`.
[Source and lowering](../../Silmaril/SSA/SeaOfNodes/Loop/MLIR/CF/Defs.lean) ·
[Scalar producer bridge](sea-of-nodes-mlir.md)

`lower` constructs an intrinsically typed `MLIR.CF.Cfg` with these blocks.

| Block | Target action |
| --- | --- |
| Entry | Run the preheader producers and pass the entry Phi operand to the header. |
| Header | Run the header producers. The true edge carries the backedge Phi operand to the header. The false edge carries the return-wire value to exit. |
| Exit | Return the singleton exit argument. |

Captured inputs remain in scope. MLIR places the latch before the captures
in the header's environment, while the source puts it after the captures.
The typed name table resolves each reference in the target's order. Header
producer values stay local to the header and cross a block boundary only
as edge operands.
[Existing CF scopes and evaluator](../../Silmaril/SSA/MLIR/CF/Basic/Defs.lean)

`lower_run` relates a budget of `b` source backedges to `b + 3` target
blocks. The allowance covers entry, up to `b` continuing header activations,
the final header test, and exit. `lower_returns_iff` preserves and reflects every finite
return across all budgets. `lower_denotePart` uses the existing embedding
into `CF.SwitchAssert` and its checked partial denotation. It identifies
the result with the native `Part` mapped to a singleton returned tuple,
with the same domain. The basic CFG embedding's terminal outcomes are
returns. `lower_diverges_iff` identifies divergence with an undefined
source result.
[Bridge theorems](../../Silmaril/SSA/SeaOfNodes/Loop/MLIR/CF/Thms.lean) ·
[Partial CFG denotation](../../Silmaril/SSA/MLIR/CF/SwitchAssert/Denotation/Thms.lean)

```lean
module
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms

open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF
open Silmaril.MLIR.Arith (Env Width)

example {Γ : List Width} {carried result : Width}
    {entrySigs headerSigs : List (List (Silmaril.SSA.SeaOfNodes.Diamond.Ty Width))}
    (g : Program Γ carried result entrySigs headerSigs) (input : Env Γ) :
    (lower g).Diverges evalOp input ↔
      ¬ (g.denote model (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).Dom :=
  lower_diverges_iff g input
```

The regression initializes the latch to `seed + 1`, adds `increment` while
the latch is unsigned-less-than `limit`, then returns `latch + seed`.
At seed 2, limit 5 and increment 1, the CFG returns 7 in five blocks.
At seed 4 and limit 5 it exits immediately and returns 9. With increment 0
and seed 2, the invariant keeps the latch at 3, so every finite budget is
exhausted and the target's partial result is `Part.none`.
[Checked example](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/MLIR/CF/Regression.lean)

The proof concerns the repository's typed pure CF fragment with fixed-width bit
vectors, its executable CFG, and its partial semantics.
[MLIR ControlFlow dialect](https://mlir.llvm.org/docs/Dialects/ControlFlowDialect/)

## Signed i64 operations shared with RTL

The bank emitter maps subtraction to flag-free `arith.subi` and signed
less-than to `arith.cmpi slt`, preserving operand order. `subi_eq_rtl` compares
the wrapped `i64` result directly. `cmpiSlt_eq_rtl` compares the `i1` result
zero-extended to RTL's predicate word. `exec_subi` and `exec_cmpiSlt` use real
RTL.SSA frame reads and preserve the entire memory. [RTL agreement][rtl-word-ops]
· [Pinned Arith operation definitions][arith-ops]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF.Thms

open Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF
open Silmaril.Machine.Lir (Binop Word)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)

example (lhs rhs : Word) :
    (Binop.cmp .lts).eval lhs rhs =
      some ((evalOp cmpiSlt (.cons lhs (.cons rhs .nil))).setWidth 64) :=
  cmpiSlt_eq_rtl lhs rhs
```

The emitted two-field bank checks the exact header operands and branches.
It continues on `-1 < 0`, passing the updated and old words, and exercises
wrapping across the signed boundary in both directions. The resized feedback
family uses this arithmetic together with typed dispatch arguments and
a checked packet readback at each positional RTL edge.
[Checked regression][signed-regression] · [Typed dispatch transport][cf-dispatch]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Loop.MLIR.CF.Regression +Silmaril.Proofs.SSA.SeaOfNodes.MLIR.Regression +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.MLIR.CF.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```

[rtl-word-ops]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/MLIR/CF/Thms.lean
[signed-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/MLIR/CF/Regression.lean
[cf-dispatch]: sea-of-nodes-guarded-feedback-rows-rtl.md#live-header-values-in-mlir-cf
[arith-ops]: https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/include/mlir/Dialect/Arith/IR/ArithOps.td
