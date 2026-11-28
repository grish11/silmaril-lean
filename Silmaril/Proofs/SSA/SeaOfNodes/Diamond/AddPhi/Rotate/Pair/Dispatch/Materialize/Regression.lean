module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (InputWord)
open AddPhi.Rotate.Pair.Dispatch (Column)
open AddPhi.Rotate.Pair.Dispatch.Materialize (Result rewrite select suffix)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word, word]
private abbrev sigs := [[wordPort], [wordPort], [wordPort], [wordPort]]

private def diamond (leftFirst leftSecond rightFirst rightSecond : BitVec 64) :
    AddPhi.Pair.Source inputs sigs where
  shared := .cons (.literal leftFirst) .nil
    (.cons (.literal leftSecond) .nil
      (.cons (.literal rightFirst) .nil (.cons (.literal rightSecond) .nil .nil)))
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms
    | .first => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (0 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil) }
    | .second => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (1 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil) }

private def withRuntimeRight (g : AddPhi.Pair.Source inputs sigs) : AddPhi.Pair.Source inputs sigs :=
  { g with arms := fun
    | .first => g.arms .first
    | .second => {
        sigs := [[wordPort]]
        dataflow := .cons .sub
          (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil)) .nil
        outputs := .cons (.output (1 : Fin 5) .head) (.cons (.output (4 : Fin 5) .head) .nil) } }

private def x : InputWord inputs := .tail (.tail .head)

private def entry (guard : Bool) (capture : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons ⟨guard⟩ (.cons (41 : BitVec 64) (.cons capture .nil))

private def observed (capture : BitVec 64) (result : Result inputs sigs) : BitVec 64 × BitVec 64 :=
  (result.denote (entry true capture), result.denote (entry false capture))

private def emitted (result : Result inputs sigs) := match result with
  | .materialized column value p => some (column, value, p)
  | .rotated _ => none

theorem keeps_the_runtime_column_and_its_local_subtraction :
    let g := withRuntimeRight (diamond 7 7 3 10)
    (rewrite g x .right).map (fun result =>
      (emitted result).map fun (column, value, p) =>
        (column, value, p.residual, p.suffix, (p.diamond.arms .second).sigs.length)) =
        .ok (some (.left, 7, x, suffix .left 7, 1)) ∧
    (rewrite g x .right).map (observed 5) = .ok ((48 : BitVec 64), (15 : BitVec 64)) :=
  ⟨rfl, rfl⟩

theorem when_both_columns_qualify_the_supplied_source_order_picks_one :
    let g := diamond 7 7 3 3
    (rewrite g x .left).map (fun result => (emitted result).map fun (column, value, _) => (column, value)) =
        .ok (some (.left, 7)) ∧
    (rewrite g x .right).map (fun result => (emitted result).map fun (column, value, _) => (column, value)) =
        .ok (some (.right, 3)) ∧
    (rewrite g x .right).map (observed 5) = .ok ((15 : BitVec 64), (15 : BitVec 64)) :=
  ⟨rfl, rfl, rfl⟩

theorem materializing_zero_keeps_the_two_add_bindings_at_this_step :
    let g := diamond 2 9 0 0
    (rewrite g x .left).map (fun result =>
      (emitted result).map fun (column, value, p) => (column, value, p.suffix.sigs.length)) =
        .ok (some (.right, 0, 3)) ∧
    (rewrite g x .left).map (observed 5) = .ok ((14 : BitVec 64), (7 : BitVec 64)) :=
  ⟨rfl, rfl⟩

theorem preserves_all_three_rotated_dispatch_results :
    let distinct := diamond 0xffffffffffffffff 0xfffffffffffffffa 3 10
    let constant := diamond 0xffffffffffffffff 0xfffffffffffffffa 3 8
    let zero := diamond 0xffffffffffffffff 0xfffffffffffffffa 1 6
    rewrite distinct x .left = (AddPhi.Rotate.Pair.Dispatch.rewrite distinct x).map .rotated ∧
    rewrite constant x .right = (AddPhi.Rotate.Pair.Dispatch.rewrite constant x).map .rotated ∧
    rewrite zero x .left = (AddPhi.Rotate.Pair.Dispatch.rewrite zero x).map .rotated :=
  ⟨rfl, rfl, rfl⟩

theorem preserves_dispatch_refusal_without_a_checked_constant :
    rewrite (withRuntimeRight (diamond 7 8 3 3)) x .left = .error .nonliteralOperand := rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Regression
