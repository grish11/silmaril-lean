module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (InputWord Program residualAdd spine)
open AddPhi.Rotate.Pair
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word)
open Silmaril.SSA.RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {g : AddPhi.Pair.Source inputs sigs} {x : InputWord inputs}
variable {target : Program inputs sigs [word]}

theorem residual_sum_eq (value : BitVec 64) (row : AddPhi.Pair.Operands) :
    residualAdd.eval model (.cons value (.cons (AddPhi.Pair.add row) .nil)) =
      spine.eval model (.cons value row) := by
  cases row with
  | cons left tail =>
    cases tail with
    | cons right tail =>
      cases tail
      exact (BitVec.add_assoc value left right).symm

theorem emitted_shape (accepted : rewrite? g x = some target) :
    target.residual = x ∧ target.suffix = residualAdd ∧
      target.diamond.shared = g.shared ∧ target.diamond.predicate = g.predicate ∧
      target.diamond.merge = g.merge := by
  obtain ⟨folded, found, rfl⟩ := Option.map_eq_some_iff.mp accepted
  obtain ⟨first, second, _, _, _, rfl⟩ := AddPhi.Pair.rewriteWith?_admission found
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem slot_eval_eq (accepted : rewrite? g x = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    target.atSlot entry slot = (original g x).atSlot entry slot := by
  obtain ⟨folded, found, rfl⟩ := Option.map_eq_some_iff.mp accepted
  change residualAdd.eval model (.cons (entry.get x)
    ((folded.arms slot).eval model entry (folded.shared.eval model entry PUnit.unit))) = _
  rw [AddPhi.Pair.rewriteWith?_slot_eval_eq found entry slot]
  exact residual_sum_eq (entry.get x) ((g.arms slot).eval model entry (g.shared.eval model entry PUnit.unit))

theorem denote_eq (accepted : rewrite? g x = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    target.denote entry = (original g x).denote entry := by
  obtain ⟨_, _, shared, predicate, merge⟩ := emitted_shape accepted
  change target.atSlot entry (target.diamond.merge.slot
    (Projection.ofBool (read model target.diamond.predicate entry
      (target.diamond.shared.eval model entry PUnit.unit)).down)) =
    (original g x).atSlot entry (g.merge.slot
      (Projection.ofBool (read model g.predicate entry (g.shared.eval model entry PUnit.unit)).down))
  rw [slot_eval_eq accepted, shared, predicate, merge]

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair
