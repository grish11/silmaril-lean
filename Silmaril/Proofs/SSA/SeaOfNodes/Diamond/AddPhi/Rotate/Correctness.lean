module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi (WordGraph WordWire)
open AddPhi.Rotate
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word)
open Silmaril.SSA.RVSDG (Tuple)

variable {inputs joined : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

theorem returns_iff_denote (p : Program inputs sigs joined)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (value : BitVec 64) :
    p.Returns entry value ↔ p.denote entry = value := by
  simp [Program.Returns, Program.denote, Arms.Graph.returns_iff_denote]
  rfl

variable {g : WordGraph inputs sigs} {x : InputWord inputs} {k : WordWire inputs sigs}
variable {target : Program inputs sigs [word]}

theorem emitted_shape (accepted : rewrite? g x k = some target) :
    target.residual = x ∧ target.suffix = residualAdd ∧
      target.diamond.shared = g.dataflow ∧ target.diamond.predicate = g.predicate ∧
      target.diamond.merge = g.phi.merge := by
  obtain ⟨folded, found, rfl⟩ := Option.map_eq_some_iff.mp accepted
  exact ⟨rfl, rfl, AddPhi.rewrite?_keeps_control found⟩

theorem slot_eval_eq (accepted : rewrite? g x k = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    target.atSlot entry slot = (original g x k).atSlot entry slot := by
  obtain ⟨folded, found, rfl⟩ := Option.map_eq_some_iff.mp accepted
  change residualAdd.eval model (.cons (entry.get x)
    ((folded.arms slot).eval model entry (folded.shared.eval model entry PUnit.unit))) = _
  rw [AddPhi.rewrite?_slot_eval_eq found entry slot]
  exact (BitVec.add_assoc _ _ _).symm

theorem denote_eq (accepted : rewrite? g x k = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    target.denote entry = (original g x k).denote entry := by
  obtain ⟨_, _, shared, predicate, merge⟩ := emitted_shape accepted
  change target.atSlot entry (target.diamond.merge.slot
    (Projection.ofBool (read model target.diamond.predicate entry
      (target.diamond.shared.eval model entry PUnit.unit)).down)) =
    (original g x k).atSlot entry (g.phi.merge.slot
      (Projection.ofBool (read model g.predicate entry (g.dataflow.eval model entry PUnit.unit)).down))
  rw [slot_eval_eq accepted, shared, predicate, merge]

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate
