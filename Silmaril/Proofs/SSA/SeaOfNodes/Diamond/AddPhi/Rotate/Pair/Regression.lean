module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi (literalArm)
open AddPhi.Rotate (InputWord Program residualAdd)
open AddPhi.Rotate.Pair (original rewrite?)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word, word]
private abbrev sigs := [[wordPort], [wordPort], [wordPort], [wordPort]]

private def diamond (first : Projection) (secondRight : BitVec 64) : AddPhi.Pair.Source inputs sigs where
  shared := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 0xfffffffffffffffa) .nil
      (.cons (.literal 3) .nil (.cons (.literal secondRight) .nil .nil)))
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
private def rotated := rewrite? (diamond .onFalse 10) x

private def entry (guard : Bool) (value : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons ⟨guard⟩ (.cons (42 : BitVec 64) (.cons value .nil))

private def observed (value : BitVec 64) (p : Program inputs sigs [word]) : BitVec 64 × BitVec 64 :=
  (p.denote (entry true value), p.denote (entry false value))

theorem emits_distinct_wrapping_sums_and_keeps_the_original_capture :
    (original (diamond .onFalse 10) x).suffix.sigs.length = 2 ∧
      rotated.map (fun p => (p.residual, p.suffix, p.diamond.arms .first, p.diamond.arms .second)) =
        some (x, residualAdd, literalArm 2, literalArm 4) :=
  ⟨rfl, rfl⟩

theorem reversal_changes_the_selected_sum_and_preserves_runtime_dependence :
    (rewrite? (diamond .onTrue 10) x).map (observed 0xffffffffffffffff) =
        some ((1 : BitVec 64), (3 : BitVec 64)) ∧
    rotated.map (observed 0xffffffffffffffff) = some ((3 : BitVec 64), (1 : BitVec 64)) ∧
    rotated.map (observed 5) = some ((9 : BitVec 64), (7 : BitVec 64)) :=
  ⟨rfl, rfl, rfl⟩

theorem the_rotation_admits_repeated_phi_operands :
    let g := diamond .onFalse 10
    let repeated := { g with arms := fun slot =>
      let arm := g.arms slot
      let wire := arm.outputs.get .head
      { arm with outputs := .cons wire (.cons wire .nil) } }
    AddPhi.Pair.rewrite? repeated = none ∧
      (rewrite? repeated x).map (fun p => (p.diamond.arms .first, p.diamond.arms .second)) =
        some (literalArm 0xfffffffffffffffe, literalArm 0xfffffffffffffff4) :=
  ⟨rfl, rfl⟩

theorem refuses_a_constant_column_or_a_folded_phi_that_would_become_constant :
    rewrite? (diamond .onFalse 3) x = none ∧ rewrite? (diamond .onFalse 8) x = none :=
  ⟨rfl, rfl⟩

theorem refuses_a_nonliteral_outer_phi_operand :
    let g := diamond .onFalse 10
    let mixed := { g with arms := fun
      | .first => g.arms .first
      | .second =>
        let arm := g.arms .second
        { arm with outputs := .cons (arm.outputs.get .head) (.cons (.arg (.tail .head)) .nil) } }
    rewrite? mixed x = none := rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Regression
