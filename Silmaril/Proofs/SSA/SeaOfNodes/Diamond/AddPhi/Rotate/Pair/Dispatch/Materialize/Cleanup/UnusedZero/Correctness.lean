module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.Defs
import Silmaril.SSA.SeaOfNodes.Pure.Deletion.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (Program residualAdd)
open AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup (cleanedSuffix)
open AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero
open Silmaril.SSA.SeaOfNodes.Pure.Deletion (delete?_outputs_eq)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p target : Program inputs sigs [word]}

theorem rewrite?_retains_diamond (accepted : rewrite? p = some target) :
    target.diamond = p.diamond ∧ target.residual = p.residual := by
  obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp accepted
  exact ⟨rfl, rfl⟩

theorem rewrite?_cleaned_shape (shape : p.suffix = cleanedSuffix) :
    rewrite? p = some { p with suffix := residualAdd } := by
  cases p with
  | mk residual diamond suffix =>
    cases shape
    rfl

theorem rewrite?_suffix_eval_eq (accepted : rewrite? p = some target)
    (entry : Tuple (Val model.value) (dataPorts [word, word])) :
    target.suffix.eval model entry = p.suffix.eval model entry := by
  obtain ⟨edit, found, rfl⟩ := Option.map_eq_some_iff.mp accepted
  obtain ⟨candidate, _, removed⟩ := Option.bind_eq_some_iff.mp found
  have outputs := delete?_outputs_eq (candidate := candidate) removed model entry PUnit.unit
  generalize edit.outputs = packet at outputs ⊢
  cases packet with
  | cons wire tail =>
    cases tail
    exact congrArg (fun values : Tuple (Val model.value) [wordPort] => values.get .head) outputs

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero
