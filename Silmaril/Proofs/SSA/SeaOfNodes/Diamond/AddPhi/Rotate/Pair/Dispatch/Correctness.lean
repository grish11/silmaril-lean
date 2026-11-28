module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (InputWord)
open AddPhi.Rotate.Pair.Dispatch
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model)
open Silmaril.SSA.RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {g : AddPhi.Pair.Source inputs sigs} {x : InputWord inputs} {result : Result inputs sigs}

theorem rewrite_eq_ok_iff :
    rewrite g x = .ok result ↔
      ∃ first second, AddPhi.Pair.literalRows? g = some (first, second) ∧
        AddPhi.Pair.nonconstantColumns first second = true ∧
        result = emit g x first second := by
  constructor
  · intro accepted
    cases rows : AddPhi.Pair.literalRows? g with
    | none =>
      simp only [rewrite, rows] at accepted
      split at accepted <;> contradiction
    | some pair =>
      obtain ⟨first, second⟩ := pair
      by_cases varying : AddPhi.Pair.nonconstantColumns first second = true
      · have emitted : emit g x first second = result := by
          simpa [rewrite, rows, varying] using accepted
        exact ⟨first, second, rfl, varying, emitted.symm⟩
      · simp [rewrite, rows, varying] at accepted
  · rintro ⟨first, second, rows, varying, rfl⟩
    simp [rewrite, rows, varying]

theorem rewrite_returns_iff (accepted : rewrite g x = .ok result)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (value : BitVec 64) :
    result.Returns entry value ↔ (AddPhi.Rotate.Pair.original g x).Returns entry value := by
  obtain ⟨first, second, rows, varying, rfl⟩ := rewrite_eq_ok_iff.mp accepted
  dsimp only [emit]
  by_cases sums : AddPhi.Pair.add first = AddPhi.Pair.add second
  · have applied : AddPhi.Rotate.Pair.Collapse.rewrite g x =
        .ok (AddPhi.Rotate.Pair.Collapse.emit g x (AddPhi.Pair.add first)) :=
      AddPhi.Rotate.Pair.Collapse.rewrite_eq_ok_iff.mpr ⟨first, second, rows, varying, sums, rfl⟩
    rw [ite_eq_left sums]
    split <;> exact AddPhi.Rotate.Pair.Collapse.rewrite_returns_iff applied entry value
  · have eligible : AddPhi.Rotate.Pair.eligible first second = true := by
      simp [AddPhi.Rotate.Pair.eligible, varying, sums]
    have applied : AddPhi.Rotate.Pair.rewrite? g x =
        some (AddPhi.Rotate.emit x (AddPhi.Pair.emit g first second)) := by
      simp [AddPhi.Rotate.Pair.rewrite?, AddPhi.Pair.rewriteWith?, rows, eligible]
    rw [ite_eq_right sums]
    exact AddPhi.Rotate.Pair.rewrite?_returns_iff applied entry value

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch
