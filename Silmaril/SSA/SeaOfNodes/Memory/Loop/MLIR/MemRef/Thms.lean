module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Correctness

/-! Exact tail selection and whole-buffer agreement for one emitted activation. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)

variable {cells : Nat} {args : List ValueSort}

/-- The emitted body finishes all memory effects before comparing its
returned word with the invariant stop word. -/
theorem lowerActivation_run (graph : Graph args) (input : Tuple (Val cells) args) (initial : Buffer cells) :
    runActivation graph input initial =
      let result := graph.body.denote input initial.cell
      (.cons (tailSelector result.1 (graph.stopWord input)) (.cons result.1 .nil), Buffer.mk result.2) :=
  Proofs.lowerActivation_run graph input initial

/-- One emitted activation agrees with the native step on exit and restart.
The buffer's cell function is the corresponding native heap in either case. -/
theorem observeActivation_eq_step (graph : Graph args) (input : Tuple (Val cells) args) (initial : Buffer cells) :
    observeActivation graph input initial = (graph.step input initial.cell).map
      (fun result => (result.1, Buffer.mk result.2)) Buffer.mk :=
  Proofs.observeActivation_eq_step graph input initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef
