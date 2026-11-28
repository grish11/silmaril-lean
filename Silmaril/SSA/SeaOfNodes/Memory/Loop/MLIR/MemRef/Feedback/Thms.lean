module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Feedback.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Feedback.Correctness

/-! Exact backedges and finite whole-buffer observations of the MemRef driver. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)

variable {args : List ValueSort} {cells : Nat}

/-- Budgeted execution agrees with the native evaluator at the same exact
backedge count, including every final cell. -/
theorem runAfter_eq_evalAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (count : Nat) (initial : Buffer cells) :
    runAfter graph input count initial = (graph.evalAfter input initial.cell count).map
      (fun result => (result.1, Buffer.mk result.2)) :=
  Proofs.runAfter_eq_evalAfter graph input count initial

/-- The counted native return and the bounded MemRef execution identify
the same word and entire final buffer. -/
theorem returnsAfter_iff_runAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (count : Nat) (initial : Buffer cells) (word : Word) (final : Buffer cells) :
    graph.ReturnsAfter input initial.cell count word final.cell ↔
      runAfter graph input count initial = some (word, final) :=
  Proofs.returnsAfter_iff_runAfter graph input count initial word final

theorem mem_observe_iff_exists_runAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Buffer cells) (result : Word × Buffer cells) :
    result ∈ observe graph input initial ↔
      ∃ count, runAfter graph input count initial = some result :=
  Proofs.mem_observe_iff_exists_runAfter graph input initial result

/-- Native and MemRef feedback preserve and reflect all finite returns. -/
theorem returns_iff_mem_observe (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Buffer cells) (word : Word) (final : Buffer cells) :
    graph.Returns input initial.cell word final.cell ↔ (word, final) ∈ observe graph input initial := by
  simp only [Graph.Returns, returnsAfter_iff_runAfter, mem_observe_iff_exists_runAfter]

/-- The partial observation is undefined exactly when no finite backedge
count produces a return. -/
theorem observe_eq_none_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Buffer cells) :
    observe graph input initial = Part.none ↔
      ∀ count, runAfter graph input count initial = none :=
  Proofs.observe_eq_none_iff graph input initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef
