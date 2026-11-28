module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi (WordGraph WordWire Result literalArm rewrite? sourceDenote)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word]
private abbrev sigs := [[wordPort], [wordPort], [wordPort]]

private def diamond (first : Projection) (offset : BitVec 64) : WordGraph inputs sigs where
  dataflow := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 7) .nil (.cons (.literal offset) .nil .nil))
  predicate := .arg .head
  phi := ⟨⟨first⟩, fun
    | .first => .output (0 : Fin 3) .head
    | .second => .output (1 : Fin 3) .head⟩

private def right : WordWire inputs sigs := .output (2 : Fin 3) .head

private def entry (guard : Bool) (payload : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons ⟨guard⟩ (.cons payload .nil)

private def observed (target : Result inputs sigs) : BitVec 64 × BitVec 64 :=
  ((target.denote model (entry true 42)).get .head, (target.denote model (entry false 43)).get .head)

theorem folds_to_distinct_arm_literals_and_wraps :
    (rewrite? (diamond .onTrue 1) right).map observed = some ((0 : BitVec 64), (8 : BitVec 64)) :=
  rfl

theorem reversed_region_order_reverses_the_selected_results :
    (rewrite? (diamond .onFalse 1) right).map observed = some ((8 : BitVec 64), (0 : BitVec 64)) :=
  rfl

theorem emits_one_folded_literal_per_original_slot :
    (rewrite? (diamond .onFalse 1) right).map (fun target => (target.arms .first, target.arms .second)) =
      some (literalArm 0, literalArm 8) :=
  rfl

theorem preserves_the_scoped_source_on_both_routes_for_arbitrary_payload (payload : BitVec 64) :
    let g := diamond .onFalse 1
    (rewrite? g right).map (fun target =>
      ((target.denote model (entry true payload)).get .head,
        (target.denote model (entry false payload)).get .head)) =
      some (sourceDenote g right (entry true payload), sourceDenote g right (entry false payload)) :=
  rfl

theorem rejects_right_zero_before_phi_push :
    rewrite? (diamond .onFalse 0) right = none := rfl

theorem rejects_a_nonliteral_phi_operand :
    let g := diamond .onFalse 1
    let mixed := { g with phi := { g.phi with operand := fun
      | .first => .arg (.tail .head)
      | .second => g.phi.operand .second } }
    rewrite? mixed right = none := rfl

theorem rejects_equal_literal_values_before_phi_push :
    let g := diamond .onTrue 1
    let equal := { g with
      dataflow := .cons (.literal 7) .nil
        (.cons (.literal 7) .nil (.cons (.literal 1) .nil .nil)) }
    rewrite? equal right = none := rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Regression
