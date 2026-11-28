module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (InputWord Program residualAdd)
open AddPhi.Rotate.Pair (original residualAdd_eval_spine)
open AddPhi.Rotate.Pair.Collapse
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model)
open Silmaril.SSA.RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {g : AddPhi.Pair.Source inputs sigs} {x : InputWord inputs}
variable {target : Program inputs sigs []}

theorem rewrite_eq_ok_iff :
    rewrite g x = .ok target ↔
      ∃ first second, AddPhi.Pair.literalRows? g = some (first, second) ∧
        AddPhi.Pair.nonconstantColumns first second = true ∧
        AddPhi.Pair.add first = AddPhi.Pair.add second ∧
        target = emit g x (AddPhi.Pair.add first) := by
  constructor
  · intro accepted
    cases rows : AddPhi.Pair.literalRows? g with
    | none => simp [rewrite, rows] at accepted
    | some pair =>
      obtain ⟨first, second⟩ := pair
      by_cases varying : AddPhi.Pair.nonconstantColumns first second = true
      · by_cases sums : AddPhi.Pair.add first = AddPhi.Pair.add second
        · simp only [rewrite, rows, varying, ite_true] at accepted
          rw [ite_eq_left sums] at accepted
          exact ⟨first, second, rfl, varying, sums, (Except.ok.inj accepted).symm⟩
        · simp [rewrite, rows, varying, sums] at accepted
      · simp [rewrite, rows, varying] at accepted
  · rintro ⟨first, second, rows, varying, sums, rfl⟩
    simp [rewrite, rows, varying, sums]

private theorem suffix_eval (value capture : BitVec 64) :
    (suffix value).eval model (.cons capture .nil) =
      residualAdd.eval model (.cons capture (.cons value .nil)) := by
  unfold suffix
  split
  · rename_i zero
    subst value
    exact (BitVec.add_zero capture).symm
  · rfl

theorem slot_eval_eq (accepted : rewrite g x = .ok target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    target.atSlot entry slot = (original g x).atSlot entry slot := by
  obtain ⟨first, second, rows, _, sums, rfl⟩ := rewrite_eq_ok_iff.mp accepted
  let actual := (g.arms slot).eval model entry (g.shared.eval model entry PUnit.unit)
  have common : AddPhi.Pair.add actual = AddPhi.Pair.add first := by
    dsimp only [actual]
    rw [AddPhi.Pair.literalRows?_slot_eval_eq rows entry slot]
    cases slot
    · rfl
    · exact sums.symm
  calc
    _ = residualAdd.eval model (.cons (entry.get x) (.cons (AddPhi.Pair.add first) .nil)) :=
      suffix_eval (AddPhi.Pair.add first) (entry.get x)
    _ = residualAdd.eval model (.cons (entry.get x) (.cons (AddPhi.Pair.add actual) .nil)) :=
      congrArg (fun sum : BitVec 64 => residualAdd.eval model (.cons (entry.get x) (.cons sum .nil))) common.symm
    _ = _ := residualAdd_eval_spine (entry.get x) actual

theorem denote_eq (accepted : rewrite g x = .ok target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    target.denote entry = (original g x).denote entry := by
  obtain ⟨first, _, _, _, _, rfl⟩ := rewrite_eq_ok_iff.mp accepted
  let slot := g.merge.slot (Projection.ofBool
    (read model g.predicate entry (g.shared.eval model entry PUnit.unit)).down)
  exact slot_eval_eq accepted entry slot

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse
