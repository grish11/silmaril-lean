module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (InputWord Program)
open AddPhi.Rotate.Pair.Dispatch.Materialize (rewrite)
open AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (Opcode model word wordPort)
open Silmaril.SSA.SeaOfNodes.GVN.Elimination (Routing)
open Silmaril.SSA.RVSDG (Address Tuple Wires)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word, word]
private abbrev sigs := [[wordPort], [wordPort]]

/-- The first occurrence is false. The second arm contains a same-shaped
local add with its own address, regardless of whether the entry has an add. -/
private def source (entryAdd sameOperand : Bool) : AddPhi.Pair.Source inputs sigs where
  shared := .cons (.literal 7) .nil
    (.cons (if entryAdd then .add else .sub)
      (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail .head)) .nil)) .nil)
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms
    | .first => {
        sigs := [], dataflow := .nil
        outputs := .cons (.arg (.tail .head)) (.cons (.output (0 : Fin 2) .head) .nil) }
    | .second => {
        sigs := [[wordPort]]
        dataflow := .cons .add
          (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail .head)) .nil)) .nil
        outputs := .cons (if sameOperand then .arg (.tail .head) else .arg (.tail (.tail .head)))
          (.cons (.output (0 : Fin 3) .head) .nil) }

private def x : InputWord inputs := .tail (.tail .head)

private def input (guard : Bool) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons ⟨guard⟩ (.cons (3 : BitVec 64) (.cons (0xffffffffffffffff : BitVec 64) .nil))

private def expected : Silmaril.SSA.SeaOfNodes.Pure.Program Opcode [word, word, word] word where
  dataflow := .cons (.literal 7) .nil
    (.cons .add (.cons (.arg (.tail .head)) (.cons (.output (0 : Fin 1) .head) .nil)) .nil)
  result := .output (1 : Fin 2) .head

theorem actual_materialization_reuses_entry_and_keeps_both_phi_occurrences :
    (rewrite (source true true) x .left).map (fun result => match result with
      | .materialized .right _ p =>
        (rewriteAt? p (.output 1 0)).map fun target =>
          (target.suffix, target.diamond.merge, target.diamond.shared, target.diamond.predicate,
            (target.diamond.arms .first).outputs.addresses, (target.diamond.arms .second).outputs.addresses,
            (target.diamond.arms .second).sigs.length, target.denote (input false), target.denote (input true))
      | _ => none) =
    .ok (some (expected, ⟨.onFalse⟩, (source true true).shared, (source true true).predicate,
      [.output 1 0, .arg 1], [.output 1 0, .arg 1], 1, 9, 9)) := rfl

private def packet : Wires OldArgs [Row, Row, Row] [wordPort, wordPort, wordPort] :=
  .cons (.output (2 : Fin 3) .head)
    (.cons (.output (1 : Fin 3) .head) (.cons (.arg (.tail .head)) .nil))

private def observations (p : Program inputs sigs [word, word]) (guard : Bool) :
    BitVec 64 × BitVec 64 × BitVec 64 :=
  let entry := slotArgs p (input guard) (if guard then .second else .first)
  let values := (Routing.wires route packet).read entry (expected.dataflow.eval model entry PUnit.unit)
  (values.get .head, values.get (.tail .head), values.get (.tail (.tail .head)))

theorem packet_keeps_original_outer_inner_and_phi_values :
    (Routing.wires route packet).addresses = [.output 1 0, .arg 1, .arg 2] ∧
    (rewrite (source true true) x .left).map (fun result => match result with
      | .materialized .right _ p =>
        (rewriteAt? p (.output 1 0)).map fun target => (observations target false, observations target true)
      | _ => none) = .ok (some ((9, 2, 3), (9, 2, 3))) :=
  ⟨rfl, rfl⟩

private def tryAt (entryAdd sameOperand : Bool) (address : Address) :=
  (rewrite (source entryAdd sameOperand) x .left).map (fun result => match result with
    | .materialized .right _ p => some (rewriteAt? p address)
    | _ => none)

theorem refuses_the_arm_local_add_and_a_different_incoming_wire :
    tryAt false true (.output 2 0) = .ok (some none) ∧
    tryAt false true (.output 1 0) = .ok (some none) ∧
    tryAt true false (.output 1 0) = .ok (some none) :=
  ⟨rfl, rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Regression
