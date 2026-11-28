module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (InputWord Program residualAdd)
open AddPhi.Rotate.Pair.Dispatch.Materialize
open AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup (Suffix cleanedSuffix)
open AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (Opcode model word wordPort)
open Silmaril.SSA.RVSDG (Tuple Wires)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word, word]
private abbrev sigs := [[wordPort], [wordPort]]
private abbrev args := dataPorts [word, word]

private def source : AddPhi.Pair.Source inputs sigs where
  shared := .cons (.literal 0) .nil (.cons (.literal 3) .nil .nil)
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms
    | .first => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil) }
    | .second => {
        sigs := [[wordPort]]
        dataflow := .cons .sub (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil)) .nil
        outputs := .cons (.output (0 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil) }

private def x : InputWord inputs := .tail (.tail .head)

private def observations {joined : List (ValueSort Unit)} (p : Program inputs sigs joined)
    (capture : BitVec 64) : BitVec 64 × BitVec 64 :=
  let entry (guard : Bool) : Tuple (Val model.value) (dataPorts inputs) :=
    .cons ⟨guard⟩ (.cons (41 : BitVec 64) (.cons capture .nil))
  (p.denote (entry false), p.denote (entry true))

theorem removes_the_actual_zero_and_keeps_reversed_phi_operands_live :
    (rewrite source x .right).map (fun intermediate =>
      (Cleanup.rewrite? intermediate).bind fun cleaned =>
        (rewrite? cleaned).map fun target =>
          (cleaned.suffix.sigs.length, target.suffix.sigs.length, target.suffix,
            target.diamond.merge, (target.diamond.arms .first).outputs.addresses,
            (target.diamond.arms .second).outputs.addresses, (target.diamond.arms .second).sigs.length,
            observations target 0xffffffffffffffff)) =
      .ok (some (2, 1, residualAdd, ⟨.onFalse⟩, [.output 1 0], [.output 2 0], 1,
        observations (AddPhi.Rotate.Pair.original source x) 0xffffffffffffffff)) ∧
    observations (AddPhi.Rotate.Pair.original source x) 0xffffffffffffffff = (2, 41) :=
  ⟨rfl, rfl⟩

private def liveOperand : Suffix where
  dataflow := .cons (.literal 0) .nil
    (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil)) .nil)
  result := .output (1 : Fin 2) .head

private def liveReturn : Suffix where
  dataflow := cleanedSuffix.dataflow
  result := .output (0 : Fin 2) .head

theorem refuses_a_surviving_operand_or_a_return_use :
    suffixEdit? liveOperand = none ∧ suffixEdit? liveReturn = none := ⟨rfl, rfl⟩

private def body : Dataflow Opcode args [] [[wordPort], [wordPort], [wordPort], [wordPort]] :=
  .cons (.literal 9) .nil
    (.cons (.literal 0) .nil
      (.cons .sub (.cons (.arg .head) (.cons (.output (0 : Fin 2) .head) .nil))
        (.cons .add (.cons (.output (2 : Fin 3) .head) (.cons (.arg (.tail .head)) .nil)) .nil)))

private def middle : GVN.Producer body word := .later .here

private def packet (readsZero : Bool) : Wires args [[wordPort], [wordPort], [wordPort], [wordPort]]
    [wordPort, wordPort] :=
  .cons (.output (3 : Fin 4) .head)
    (.cons (if readsZero then .output (1 : Fin 4) .head else .output (0 : Fin 4) .head) .nil)

theorem remaps_an_interior_deletion_and_checks_the_second_packet_field :
    (Pure.Deletion.delete? middle (packet false)).map (fun edit =>
      (Pure.Deletion.opcodes edit.erasure.flow, edit.outputs.addresses,
        (edit.erasure.route middle.origin).isNone,
        (edit.erasure.route (.output (2 : Fin 4) .head)).map (fun wire => wire.address))) =
      some ([⟨[], word, .literal 9⟩, ⟨[word, word], word, .sub⟩, ⟨[word, word], word, .add⟩],
        [.output 2 0, .output 0 0], true, some (.output 1 0)) ∧
    Pure.Deletion.delete? middle (packet true) = none :=
  ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.Regression
