module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair

open Pure.SubZero (model word)
open RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {g : AddPhi.Pair.Source inputs sigs} {x : InputWord inputs}
variable {target : Program inputs sigs [word]}

/-- The residual add to a folded row implements the original two-add suffix. -/
theorem residualAdd_eval_spine (value : BitVec 64) (row : AddPhi.Pair.Operands) :
    residualAdd.eval model (.cons value (.cons (AddPhi.Pair.add row) .nil)) =
      spine.eval model (.cons value row) :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.residual_sum_eq value row

/-- Keep the original residual capture and control, and emit one suffix add. -/
theorem rewrite?_emitted_shape (accepted : rewrite? g x = some target) :
    target.residual = x ∧ target.suffix = residualAdd ∧
      target.diamond.shared = g.shared ∧ target.diamond.predicate = g.predicate ∧
      target.diamond.merge = g.merge :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.emitted_shape accepted

/-- At each original Region occurrence, both suffixes return the same wrapping word. -/
theorem rewrite?_slot_eval_eq (accepted : rewrite? g x = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    target.atSlot entry slot = (original g x).atSlot entry slot :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.slot_eval_eq accepted entry slot

/-- The emitted graph and residual add preserve the result at every typed entry. -/
theorem rewrite?_denote_eq (accepted : rewrite? g x = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    target.denote entry = (original g x).denote entry :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.denote_eq accepted entry

/-- The native finite returns agree in both directions. -/
theorem rewrite?_returns_iff (accepted : rewrite? g x = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (value : BitVec 64) :
    target.Returns entry value ↔ (original g x).Returns entry value := by
  rw [Program.returns_iff_denote, Program.returns_iff_denote, rewrite?_denote_eq accepted]

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair
