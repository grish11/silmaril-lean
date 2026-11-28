module

import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Regression

open Silmaril.SSA.SeaOfNodes
open Diamond (Ty ValueSort)
open GVN.Cyclic.Activation (Inputs)
open GVN.Cyclic.FixedPoint (normalize)
open GVN.Cyclic.Pass (proposals tryProposal?)
open GVN.Cyclic.Builder (build?)
open GVN.Cyclic.Builder.Preheader
open Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Port)
open scoped Pure.WordNormalize

private abbrev inputs : List (ValueSort Unit) := [.predicate, .predicate, word, word]
private abbrev carried : List (ValueSort Unit) := [.predicate, word, word]
private abbrev preheaderSigs : List (List (Ty Unit)) := [[wordPort], [wordPort]]
private abbrev headerSigs : List (List (Ty Unit)) := [[wordPort], [wordPort], [wordPort], [wordPort]]

private def y : Port (Diamond.dataPorts inputs) wordPort := .tail (.tail .head)
private def z : Port (Diamond.dataPorts inputs) wordPort := .tail (.tail (.tail .head))
private def a : Port carried word := .tail .head
private def b : Port carried word := .tail (.tail .head)

private def fixture (sameChild sameFeedback : Bool) : Native inputs carried preheaderSigs headerSigs word where
  preheader := .cons .add (.cons (.arg y) (.cons (.arg z) .nil))
    (.cons .add (.cons (.arg y) (.cons (.arg (if sameChild then z else y)) .nil)) .nil)
  header := .cons (.literal 1) .nil
    (.cons .add (.cons (.arg (.tail (.tail (.tail (.tail (.tail .head)))))) (.cons (.output (0 : Fin 1) .head) .nil))
      (.cons .add
        (.cons (.arg (.tail (.tail (.tail (.tail (.tail (.tail .head))))))) (.cons (.output (0 : Fin 2) .head) .nil))
        (.cons .add (.cons (.output (1 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil)) .nil)))
  phiInputs
    | .entry => .cons (.arg .head) (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))
    | .backedge =>
      .cons (.arg (.tail .head)) (.cons (.output (3 : Fin 4) .head)
        (.cons (if sameFeedback then .output (3 : Fin 4) .head else .arg (.tail (.tail .head))) .nil))
  predicate := .arg (.tail (.tail (.tail (.tail .head))))
  result := .output (3 : Fin 4) .head

private def input : Inputs model inputs :=
  .cons ⟨true⟩ (.cons ⟨false⟩ (.cons (3 : BitVec 64) (.cons (4 : BitVec 64) .nil)))

private def phiMembers (sameChild sameFeedback : Bool) : Option Bool :=
  (build? (prepare (fixture sameChild sameFeedback))).map fun built =>
    let partition := GVN.Cyclic.FixedPoint.normalize built.graph
    decide (partition ⟨1, by change 1 < 7; decide⟩ = partition ⟨2, by change 2 < 7; decide⟩)

theorem distinct_native_producers_share_a_preheader_id_and_capture :
    let loop := fixture true true
    (build? loop).isNone = true ∧
      (loop.phiInputs .entry).addresses = [.arg 0, .output 0 0, .output 1 0] ∧
      (laneId loop (number loop) a, laneId loop (number loop) b) = (2, 2) ∧
      ((prepare loop).phiInputs .entry).addresses = [.arg 0, .arg 1, .arg 1] ∧ phiMembers true true = some true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem changed_child_and_different_feedback_keep_classes_separate :
    phiMembers false true = some false ∧ phiMembers true false = some false ∧
      (optimize? (fixture false true)).isNone = true ∧ (optimize? (fixture true false)).isNone = true :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem actual_rewrite_deletes_one_binding_and_keeps_packet_and_return :
    let loop := fixture true true
    (optimize? loop).map (fun edited =>
      (edited.headerSigs.length, (edited.graph.phiInputs .entry).addresses, (edited.graph.phiInputs .backedge).addresses,
        edited.graph.step model input (edited.graph.initial model input),
        edited.graph.evalBackedges model 0 input, edited.graph.evalBackedges model 1 input)) =
      some (3, [.arg 0, .output 0 0, .output 1 0], [.arg 1, .output 2 0, .output 2 0],
        .inr (.cons ⟨false⟩ (.cons (16 : BitVec 64) (.cons (16 : BitVec 64) .nil))), none, some (34 : BitVec 64)) ∧
      loop.step model input (loop.initial model input) =
        .inr (.cons ⟨false⟩ (.cons (16 : BitVec 64) (.cons (16 : BitVec 64) .nil))) ∧
      loop.evalBackedges model 0 input = none ∧ loop.evalBackedges model 1 input = some (34 : BitVec 64) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Enumerate the real pass proposals and count checked deletions before
and after native restoration. The first number includes refused proposals. -/
private def proposalScan (sameFeedback : Bool) : Option (Nat × Nat × Nat) := do
  let loop := fixture true sameFeedback
  let built ← build? (prepare loop)
  let candidates := proposals built.view
  let partition := normalize built.graph
  let deleted := candidates.filterMap (tryProposal? built.view partition)
  pure (candidates.length, deleted.length, (deleted.filterMap (restore? loop)).length)

theorem enumeration_restores_every_accepted_deletion :
    proposalScan true = some (16, 2, 2) ∧ proposalScan false = some (16, 0, 0) :=
  ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Regression
