module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi (Result literalArm)
open AddPhi.Pair (Source rewrite? sourceDenote)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word]
private abbrev sigs := [[wordPort], [wordPort], [wordPort]]

private def diamond (first : Projection) (secondRight : BitVec 64) : Source inputs sigs where
  shared := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 0xfffffffffffffffa) .nil (.cons (.literal 3) .nil .nil))
  predicate := .arg .head
  merge := ⟨first⟩
  arms
    | .first => {
        sigs := []
        dataflow := .nil
        outputs := .cons (.output (0 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil) }
    | .second => {
        sigs := [[wordPort]]
        dataflow := .cons (.literal secondRight) .nil .nil
        outputs := .cons (.output (1 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil) }

private def entry (guard : Bool) (payload : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons ⟨guard⟩ (.cons payload .nil)

private def observed (target : Result inputs sigs) : BitVec 64 × BitVec 64 :=
  ((target.denote model (entry true 42)).get .head, (target.denote model (entry false 43)).get .head)

theorem each_occurrence_gets_its_own_asymmetric_wrapping_sum :
    (rewrite? (diamond .onFalse 10)).map (fun target => (target.arms .first, target.arms .second)) =
      some (literalArm 2, literalArm 4) := rfl

theorem reversing_the_region_preserves_pairs_but_changes_the_selected_slot :
    (rewrite? (diamond .onTrue 10)).map observed = some ((2 : BitVec 64), (4 : BitVec 64)) ∧
    (rewrite? (diamond .onFalse 10)).map observed = some ((4 : BitVec 64), (2 : BitVec 64)) :=
  ⟨rfl, rfl⟩

theorem reversed_region_agrees_with_the_native_join_for_both_routes (payload : BitVec 64) :
    let g := diamond .onFalse 10
    (rewrite? g).map (fun target =>
      ((target.denote model (entry true payload)).get .head,
        (target.denote model (entry false payload)).get .head)) =
      some (sourceDenote g (entry true payload), sourceDenote g (entry false payload)) :=
  rfl

theorem rejects_a_runtime_operand_on_the_second_occurrence :
    let g := diamond .onFalse 10
    let mixed := { g with arms := fun
      | .first => g.arms .first
      | .second =>
        let arm := g.arms .second
        { arm with outputs := .cons (arm.outputs.get .head) (.cons (.arg (.tail .head)) .nil) } }
    rewrite? mixed = none := rfl

theorem rejects_a_right_column_whose_phi_would_become_constant :
    rewrite? (diamond .onFalse 3) = none := rfl

theorem rejects_identical_columns_at_the_doubling_boundary :
    let g := diamond .onFalse 10
    let repeated := { g with arms := fun slot =>
      let arm := g.arms slot
      let wire := arm.outputs.get .head
      { arm with outputs := .cons wire (.cons wire .nil) } }
    rewrite? repeated = none := rfl

theorem equal_folded_results_still_represent_the_fresh_phi :
    (rewrite? (diamond .onFalse 8)).map observed = some ((2 : BitVec 64), (2 : BitVec 64)) := rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Regression
