module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi (WordGraph WordWire literalArm)
open AddPhi.Rotate
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word, word]
private abbrev sigs := [[wordPort], [wordPort], [wordPort]]

private def diamond (offset : BitVec 64) : WordGraph inputs sigs where
  dataflow := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 7) .nil (.cons (.literal offset) .nil .nil))
  predicate := .arg .head
  phi := ⟨⟨.onFalse⟩, fun
    | .first => .output (0 : Fin 3) .head
    | .second => .output (1 : Fin 3) .head⟩

private def x : InputWord inputs := .tail (.tail .head)
private def k : WordWire inputs sigs := .output (2 : Fin 3) .head

private def entry (guard : Bool) (value : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons ⟨guard⟩ (.cons (42 : BitVec 64) (.cons value .nil))

private def rotated := rewrite? (diamond 2) x k

theorem emits_one_add_after_the_folded_phi :
    (original (diamond 2) x k).suffix.sigs.length = 2 ∧
      rotated.map (fun p => (p.residual, p.suffix)) = some (x, residualAdd) :=
  ⟨rfl, rfl⟩

theorem folds_each_occurrence_in_the_original_region_order :
    rotated.map (fun p => (p.diamond.arms .first, p.diamond.arms .second)) =
      some (literalArm 1, literalArm 9) := rfl

theorem returns_on_the_reversed_region_and_reads_the_runtime_capture :
    rotated.map (fun p =>
      (p.denote (entry false 0xffffffffffffffff), p.denote (entry true 0xffffffffffffffff),
        p.denote (entry false 5), p.denote (entry true 5))) =
      some ((0 : BitVec 64), (8 : BitVec 64), (6 : BitVec 64), (14 : BitVec 64)) := rfl

theorem refuses_right_zero_before_the_rotated_branch :
    rewrite? (diamond 0) x k = none := rfl

theorem refuses_a_phi_that_would_materialize_a_constant :
    let g := diamond 2
    let equal := { g with
      dataflow := .cons (.literal 7) .nil
        (.cons (.literal 7) .nil (.cons (.literal 2) .nil .nil)) }
    rewrite? equal x k = none := rfl

theorem refuses_a_runtime_outer_right_wire :
    rewrite? (diamond 2) x (.arg (.tail .head)) = none := rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Regression
