module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (InputWord Program)
open AddPhi.Rotate.Pair.Collapse (addConstant returnCapture rewrite)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word, word]
private abbrev sigs := [[wordPort], [wordPort], [wordPort], [wordPort]]

private def diamond (first : Projection) (rightFirst rightSecond : BitVec 64) :
    AddPhi.Pair.Source inputs sigs where
  shared := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 0xfffffffffffffffa) .nil
      (.cons (.literal rightFirst) .nil (.cons (.literal rightSecond) .nil .nil)))
  predicate := .arg .head
  merge := ⟨first⟩
  arms
    | .first => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (0 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil) }
    | .second => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (1 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil) }

private def x : InputWord inputs := .tail (.tail .head)
private def collapsed := rewrite (diamond .onFalse 3 8) x

private def entry (guard : Bool) (value : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons ⟨guard⟩ (.cons (42 : BitVec 64) (.cons value .nil))

private def observed (value : BitVec 64) (p : Program inputs sigs []) : BitVec 64 × BitVec 64 :=
  (p.denote (entry true value), p.denote (entry false value))

theorem materializes_one_wrapping_literal_after_the_join :
    collapsed.map (fun p => (p.residual, p.suffix, (p.diamond.arms .first).sigs, (p.diamond.arms .second).sigs)) =
      .ok (x, addConstant 2, [], []) := rfl

theorem reversed_region_keeps_both_routes_and_the_same_wrapping_result :
    (rewrite (diamond .onTrue 3 8) x).map (fun p => (p.diamond.merge.first, observed 0xffffffffffffffff p)) =
        .ok (.onTrue, ((1 : BitVec 64), (1 : BitVec 64))) ∧
    collapsed.map (fun p => (p.diamond.merge.first, observed 0xffffffffffffffff p)) =
        .ok (.onFalse, ((1 : BitVec 64), (1 : BitVec 64))) ∧
    collapsed.map (observed 5) = .ok ((7 : BitVec 64), (7 : BitVec 64)) :=
  ⟨rfl, rfl, rfl⟩

theorem zero_sum_uses_the_immediate_right_zero_branch :
    let zero := rewrite (diamond .onFalse 1 6) x
    zero.map (fun p => (p.residual, p.suffix, p.suffix.sigs.length)) = .ok (x, returnCapture, 0) ∧
    zero.map (observed 5) = .ok ((5 : BitVec 64), (5 : BitVec 64)) :=
  ⟨rfl, rfl⟩

theorem originally_constant_columns_take_priority_over_equal_sums :
    let g := diamond .onFalse 3 8
    let constantColumns := { g with
      shared := .cons (.literal 7) .nil
        (.cons (.literal 7) .nil (.cons (.literal 3) .nil (.cons (.literal 3) .nil .nil))) }
    rewrite constantColumns x = .error .constantOriginalColumn := rfl

theorem unequal_sums_stay_with_the_existing_rotation :
    let g := diamond .onFalse 3 10
    rewrite g x = .error .differentSums ∧ (AddPhi.Rotate.Pair.rewrite? g x).isSome = true :=
  ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.Regression
