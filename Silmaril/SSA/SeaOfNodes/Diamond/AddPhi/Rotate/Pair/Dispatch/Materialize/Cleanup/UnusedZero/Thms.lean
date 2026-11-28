module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero

open Pure.SubZero (model word)
open RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p target : Program inputs sigs [word]}

/-- The original guard, ordered Region and each live Φ wire and its
producer scope are retained along with the runtime capture. -/
theorem rewrite?_retains_diamond (accepted : rewrite? p = some target) :
    target.diamond = p.diamond ∧ target.residual = p.residual :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.rewrite?_retains_diamond accepted

/-- The actual suffix emitted by the inner-add cleanup becomes one
addition of the capture and surviving Φ, in operand order. -/
theorem rewrite?_cleaned_shape (shape : p.suffix = cleanedSuffix) :
    rewrite? p = some { p with suffix := residualAdd } :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.rewrite?_cleaned_shape shape

/-- The rewritten suffix preserves its result for every typed input tuple. -/
theorem rewrite?_suffix_eval_eq (accepted : rewrite? p = some target)
    (entry : Tuple (Val model.value) (dataPorts [word, word])) :
    target.suffix.eval model entry = p.suffix.eval model entry :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.rewrite?_suffix_eval_eq accepted entry

/-- No predecessor occurrence changes its result. -/
theorem rewrite?_atSlot_eq (accepted : rewrite? p = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    target.atSlot entry slot = p.atSlot entry slot := by
  have ⟨diamond, residual⟩ := rewrite?_retains_diamond accepted
  rw [Program.atSlot, Program.atSlot, diamond, residual, rewrite?_suffix_eval_eq accepted]

/-- The deletion preserves and reflects all finite returns of the input program. -/
theorem rewrite?_returns_iff (accepted : rewrite? p = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    target.Returns entry returned ↔ p.Returns entry returned := by
  have ⟨diamond, residual⟩ := rewrite?_retains_diamond accepted
  simp only [Program.Returns, diamond, residual, rewrite?_suffix_eval_eq accepted]

/-- Materialization, inner-add cleanup and zero deletion preserve and
reflect every typed finite return of the original two-Φ program. -/
theorem materialize_then_cleanup_returns_iff {g : AddPhi.Pair.Source inputs sigs}
    {x : InputWord inputs} {first : Column} {intermediate : Result inputs sigs}
    (materialized : Materialize.rewrite g x first = .ok intermediate)
    (cleaned : Cleanup.rewrite? intermediate = some p) (deleted : rewrite? p = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    target.Returns entry returned ↔ (original g x).Returns entry returned :=
  (rewrite?_returns_iff deleted entry returned).trans
    (Cleanup.materialize_then_rewrite?_returns_iff materialized cleaned entry returned)

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero
