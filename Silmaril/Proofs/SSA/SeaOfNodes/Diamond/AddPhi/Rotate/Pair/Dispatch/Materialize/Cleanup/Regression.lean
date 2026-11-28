module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (InputWord Program)
open AddPhi.Rotate.Pair.Dispatch (Column)
open AddPhi.Rotate.Pair.Dispatch.Materialize (rewrite suffix)
open AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup (cleanedSuffix rewrite?)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word, word]
private abbrev sigs := [[wordPort], [wordPort], [wordPort], [wordPort]]

private def fixture (leftFirst leftSecond rightFirst rightSecond : BitVec 64) :
    AddPhi.Pair.Source inputs sigs where
  shared := .cons (.literal leftFirst) .nil (.cons (.literal leftSecond) .nil
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

private def liveRight (value : BitVec 64) : AddPhi.Pair.Source inputs sigs :=
  { fixture value value 3 10 with arms := fun
    | .first => (fixture value value 3 10).arms .first
    | .second => {
        sigs := [[wordPort]]
        dataflow := .cons .sub
          (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil)) .nil
        outputs := .cons (.output (1 : Fin 5) .head) (.cons (.output (4 : Fin 5) .head) .nil) } }

private def x : InputWord inputs := .tail (.tail .head)

private def entry (guard : Bool) (capture : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons ⟨guard⟩ (.cons (41 : BitVec 64) (.cons capture .nil))

private def observations {joined : List (ValueSort Unit)} (p : Program inputs sigs joined) (capture : BitVec 64) : BitVec 64 × BitVec 64 :=
  (p.denote (entry true capture), p.denote (entry false capture))

theorem rewrites_the_actual_suffix_and_retains_each_surviving_occurrence :
    (rewrite (liveRight 0) x .right).map (fun result =>
      (rewrite? result).map fun target =>
        (target.suffix.sigs.length, target.suffix, target.residual, target.diamond.merge,
          (target.diamond.arms .first).outputs.addresses,
          (target.diamond.arms .second).outputs.addresses,
          (target.diamond.arms .second).sigs.length)) =
      .ok (some (2, cleanedSuffix, x, ⟨.onFalse⟩, [.output 2 0], [.output 4 0], 1)) := rfl

theorem live_subtraction_and_wraparound_agree_with_the_original :
    (rewrite (liveRight 0) x .right).map (fun result =>
      (rewrite? result).map fun target => (observations target 5, observations target 0xffffffffffffffff)) =
      .ok (some ((41, 8), (41, 2))) ∧
    (observations (AddPhi.Rotate.Pair.original (liveRight 0) x) 5,
      observations (AddPhi.Rotate.Pair.original (liveRight 0) x) 0xffffffffffffffff) =
      ((41, 8), (41, 2)) := ⟨rfl, rfl⟩

theorem nonzero_and_outer_zero_are_refused :
    (rewrite (liveRight 7) x .right).map rewrite? = .ok none ∧
    (rewrite (fixture 2 9 0 0) x .left).map rewrite? = .ok none := ⟨rfl, rfl⟩

theorem a_left_tag_cannot_substitute_for_the_actual_inner_rhs :
    rewrite? (.materialized .left 0
      { AddPhi.Rotate.Pair.Dispatch.Materialize.emit (liveRight 0) x .left 0 with
        suffix := suffix .right 0 }) = none := rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.Regression
