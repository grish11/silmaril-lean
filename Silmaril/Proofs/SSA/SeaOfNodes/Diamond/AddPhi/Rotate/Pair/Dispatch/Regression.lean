module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi (literalArm)
open AddPhi.Rotate (InputWord residualAdd)
open AddPhi.Rotate.Pair.Collapse (addConstant returnCapture)
open AddPhi.Rotate.Pair.Dispatch (Result rewrite)
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

private def entry (guard : Bool) (value : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons ⟨guard⟩ (.cons (42 : BitVec 64) (.cons value .nil))

private def observed (value : BitVec 64) (result : Result inputs sigs) : BitVec 64 × BitVec 64 :=
  (result.denote (entry true value), result.denote (entry false value))

theorem distinct_sums_emit_the_typed_phi_with_the_residual_add :
    (rewrite (diamond .onFalse 3 10) x).map (fun
      | .residualPhi p => some (p.residual, p.suffix, p.diamond.arms .first, p.diamond.arms .second)
      | _ => none) = .ok (some (x, residualAdd, literalArm 2, literalArm 4)) := rfl

theorem reversed_occurrence_order_changes_the_selected_sum :
    (rewrite (diamond .onTrue 3 10) x).map (observed 5) = .ok ((7 : BitVec 64), (9 : BitVec 64)) ∧
    (rewrite (diamond .onFalse 3 10) x).map (observed 5) = .ok ((9 : BitVec 64), (7 : BitVec 64)) :=
  ⟨rfl, rfl⟩

theorem equal_nonzero_sums_emit_one_constant_and_add :
    (rewrite (diamond .onFalse 3 8) x).map (fun
      | .constantAdd p => some (p.residual, p.suffix)
      | _ => none) = .ok (some (x, addConstant 2)) ∧
    (rewrite (diamond .onFalse 3 8) x).map (observed 0xffffffffffffffff) =
      .ok ((1 : BitVec 64), (1 : BitVec 64)) :=
  ⟨rfl, rfl⟩

theorem equal_zero_sums_emit_only_the_capture :
    (rewrite (diamond .onFalse 1 6) x).map (fun
      | .captureOnly p => some (p.residual, p.suffix, p.suffix.sigs.length)
      | _ => none) = .ok (some (x, returnCapture, 0)) :=
  rfl

theorem repeated_phi_columns_are_eligible_for_the_rotation :
    let g := diamond .onFalse 3 10
    let repeated := { g with arms := fun slot =>
      let arm := g.arms slot
      let wire := arm.outputs.get .head
      { arm with outputs := .cons wire (.cons wire .nil) } }
    (rewrite repeated x).map (observed 1) =
      .ok ((0xfffffffffffffff5 : BitVec 64), (0xffffffffffffffff : BitVec 64)) :=
  rfl

private def runtimeRight (g : AddPhi.Pair.Source inputs sigs) : AddPhi.Pair.Source inputs sigs :=
  { g with arms := fun
    | .first => g.arms .first
    | .second =>
      let arm := g.arms .second
      { arm with outputs := .cons (arm.outputs.get .head) (.cons (.arg (.tail .head)) .nil) } }

theorem reports_nonliteral_refusal_and_earlier_priority_separately :
    let g := diamond .onFalse 3 8
    let constantLeft := { g with
      shared := .cons (.literal 7) .nil
        (.cons (.literal 7) .nil (.cons (.literal 3) .nil (.cons (.literal 8) .nil .nil))) }
    rewrite (runtimeRight g) x = .error .nonliteralOperand ∧
    rewrite constantLeft x = .error .constantColumnPriority ∧
    rewrite (runtimeRight constantLeft) x = .error .constantColumnPriority ∧
    rewrite (diamond .onFalse 0 0) x = .error .constantColumnPriority :=
  ⟨rfl, rfl, rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Regression
