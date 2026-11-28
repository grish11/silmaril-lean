# Native preheader-seeded GVN in typed MLIR CF

Import `Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR.Thms`.
Use `emit? g` for the original native single-latch loop and
`emitNormalized? g` for the actual graph returned by the existing
executable normalization driver. Both calls construct a typed
`MLIR.CF.Cfg` with an entry block, a `cf.cond_br` header, and a
singleton word exit. Admission checks both producer tables for
wrapping `i64` constants, addition and multiplication. It returns
`none` for subtraction. Predicate captures and carried lanes are
encoded as `i1`.
[Native adapter](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Iteration/Preheader/MLIR/Defs.lean) ·
[Mixed-bank CF lowering](../../Silmaril/SSA/SeaOfNodes/Loop/MLIR/CF/Mixed/Defs.lean)

`inputEnv` encodes the original captures in their original order.
The entry edge passes the complete ordered entry Φ packet, and the
header name scope keeps the captures available alongside the carried
block arguments. `emit_normalized_entry_eq` proves equality of the
actual typed entry blocks, including the preheader instructions and
entry edge operands. The lowering's header simulation reads the
original predicate and sends every ordered feedback value on the true
edge or the result word on the false edge.
[CF lowering laws](../../Silmaril/SSA/SeaOfNodes/Loop/MLIR/CF/Mixed/Thms.lean) ·
[Public emission laws](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Iteration/Preheader/MLIR/Thms.lean)

`emit_normalized_run_eq` compares both admitted CFGs at every block
budget. The source-to-CF simulation uses `b + 3` CF blocks for `b`
native backedges. The extra blocks account for entry, the final header
test, and exit. `emit_normalized_returns_iff` relates existential bounds
for the two artifacts, and `emit_normalized_diverges_iff` compares
absence of a return over all finite block budgets.

```lean
module
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR.Thms

open Silmaril.SSA.SeaOfNodes
open Diamond (ValueSort)
open GVN.Cyclic.Activation (Inputs)
open GVN.Cyclic.Builder.Preheader (Native)
open GVN.Cyclic.Iteration.Preheader.MLIR
open Pure.SubZero (model word)
open Loop.MLIR.CF (evalOp)

example {args carried : List (ValueSort Unit)}
    {entry header : List (List (Diamond.Ty Unit))}
    (g : Native args carried entry header word)
    (original normalized : Artifact args carried)
    (h₁ : emit? g = some original) (h₂ : emitNormalized? g = some normalized)
    (input : Inputs model args) (bits : BitVec 64)
    (returns : ∃ fuel, original.run evalOp fuel (inputEnv input) = some (.cons bits .nil)) :
    ∃ fuel, normalized.run evalOp fuel (inputEnv input) = some (.cons bits .nil) :=
  (emit_normalized_returns_iff h₁ h₂ input bits).mpr returns
```

The existing native fixture produces CF headers of sizes 5, 4, and 3
across its two deletions. With captures `(true, false, 3, 4)`, the entry
edge passes `(true, 7, 7, 7)` and the original and normalized CFG runs
independently return `99` at bounds 4 and 5. With captures
`(true, true, 3, 4)`, neither artifact has a finite return. A native
preheader containing subtraction is refused by this adapter.
[Fixture and checks](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/Iteration/Preheader/Regression.lean)

```sh
topic=SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader
make check CHECK_TARGETS="+Silmaril.$topic.MLIR.Thms +Silmaril.Proofs.$topic.Regression"
lake env leanchecker "Silmaril.$topic.MLIR.Thms"
lake env leanchecker "Silmaril.Proofs.$topic.Regression"
```

Click PLDI ’95 §3.1 step 3 motivates replacing redundant producers before
lowering. This bridge covers the admitted native word-result profile
and the finite observation in the repository's typed CF semantics.
External MLIR serialization or execution, SCF emission, and completeness
of GVN on arbitrary CFGs are outside its scope.
[Pinned Click paper](sea-of-nodes-gvn-cyclic-pass.md#sources) ·
[MLIR CF operations in LLVM 20.1.8](https://github.com/llvm/llvm-project/blob/llvmorg-20.1.8/mlir/include/mlir/Dialect/ControlFlow/IR/ControlFlowOps.td)
