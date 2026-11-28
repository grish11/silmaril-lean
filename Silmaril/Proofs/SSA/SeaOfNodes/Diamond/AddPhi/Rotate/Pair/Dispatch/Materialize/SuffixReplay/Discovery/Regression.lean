module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.Defs
import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (InputWord Program residualAdd)
open AddPhi.Rotate.Pair.Dispatch.Materialize
open AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay (blockOf)
open AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery (normalize)
open Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay (Block)
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay (findProducer?)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (Opcode model word wordPort)
open Silmaril.SSA.SeaOfNodes.GVN (Producer newest weaken)
open Silmaril.SSA.RVSDG (Origin Tuple Wires extend)

open Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery (Edit unused? step? addCount leftLiteralCount)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word, word]
private abbrev sigs := [[wordPort], [wordPort]]

private def sourceWith (right : BitVec 64) : AddPhi.Pair.Source inputs sigs where
  shared := .cons (.literal 3) .nil (.cons (.literal right) .nil .nil)
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms
    | .first => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil) }
    | .second => {
        sigs := [[wordPort]]
        dataflow := .cons .sub (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil)) .nil
        outputs := .cons (.output (2 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil) }

private def source := sourceWith 0

private def x : InputWord inputs := .tail (.tail .head)

private def observe {joined : List (ValueSort Unit)} (p : Program inputs sigs joined) (guard : Bool) :
    BitVec 64 :=
  let entry : Tuple (Val model.value) (dataPorts inputs) :=
    .cons ⟨guard⟩ (.cons (41 : BitVec 64) (.cons (0xffffffffffffffff : BitVec 64) .nil))
  p.denote entry

theorem redirection_exposes_literal_deletion_in_the_actual_suffix :
    (rewrite source x .left).map (fun result => match result with
      | .materialized .right _ p =>
        let before := (Cleanup.UnusedZero.leadingZero? p.suffix).map fun zero =>
          (unused? (blockOf p) zero).isNone
        let run := Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize (blockOf p)
        let target := normalize p
        some (before, run.rules, target.suffix, target.diamond.merge,
          (target.diamond.arms .first).outputs.addresses, (target.diamond.arms .second).outputs.addresses,
          observe target false, observe target true)
      | _ => none) =
      .ok (some (some true, [.rightZero, .deleteUnused], residualAdd, ⟨.onFalse⟩,
        [.output 0 0], [.output 2 0],
        observe (AddPhi.Rotate.Pair.original source x) false, observe (AddPhi.Rotate.Pair.original source x) true)) ∧
    (observe (AddPhi.Rotate.Pair.original source x) false, observe (AddPhi.Rotate.Pair.original source x) true) =
      (2, 41) := ⟨rfl, rfl⟩

private def packetExample (keepZero : Bool) : Block [word] [wordPort] where
  sigs := [[wordPort], [wordPort]]
  flow := .cons (.literal 0) .nil
    (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil)) .nil)
  packet := .cons (.output (1 : Fin 2) .head)
    (.cons (if keepZero then .output (0 : Fin 2) .head else .arg .head) .nil)

private def packetSummary (keepZero : Bool) :=
  let final := Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize (packetExample keepZero)
  (final.rules, final.state.block.sigs.length, final.state.block.packet.addresses)

theorem second_packet_field_keeps_the_literal_live_after_redirection :
    packetSummary true = ([.rightZero], 1, [.arg 0, .output 0 0]) ∧
    packetSummary false = ([.rightZero, .deleteUnused], 0, [.arg 0, .arg 0]) := ⟨rfl, rfl⟩

private def literalPriority : Block [] [] where
  sigs := [[wordPort], [wordPort], [wordPort]]
  flow := .cons (.literal 5) .nil (.cons (.literal 0) .nil
    (.cons .add (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil)) .nil))
  packet := .cons (.output (2 : Fin 3) .head) .nil

theorem higher_priority_literal_fold_keeps_the_table_size :
    (step? literalPriority).map (fun edit =>
      (edit.rule, edit.state.block.sigs.length, addCount edit.state.block)) =
        some (.literal, 3, 0) := rfl

private abbrev args := dataPorts [word, word]
private abbrev row := [wordPort]

private abbrev TestTail (past : List (List (Ty Unit))) :=
  Σ sigs, Dataflow Opcode args past sigs × Wires args (extend past sigs) [wordPort, wordPort]

private def appendTail (build : ∀ past, Origin args past wordPort → TestTail past) :
    {past sigs : List (List (Ty Unit))} →
    Dataflow Opcode args past sigs → Origin args (extend past sigs) wordPort → TestTail past
  | past, _, .nil, old => build past old
  | _, _, .cons opcode operands rest, old =>
    let ⟨_, flow, packet⟩ := appendTail build rest old
    ⟨_, .cons opcode operands flow, packet⟩

private def withTail (p : Program inputs sigs [word])
    (build : ∀ past, Origin args past wordPort → TestTail past) : Block [word, word] [wordPort] :=
  let ⟨sigs, flow, packet⟩ := appendTail build p.suffix.dataflow p.suffix.result
  ⟨sigs, flow, packet⟩

/-- Test-only tail on the actual emitted table: add the wrapping sum to the
old result and make the sum itself the other outgoing value. -/
private def wrappingAdd (past : List (List (Ty Unit))) (old : Origin args past wordPort) : TestTail past :=
  let maxWire : Origin args (past ++ [row]) wordPort := newest .head
  let oneWire : Origin args ((past ++ [row]) ++ [row]) wordPort := newest .head
  let sumWire : Origin args (((past ++ [row]) ++ [row]) ++ [row]) wordPort := newest .head
  let old := weaken row (weaken row (weaken row old))
  ⟨[row, row, row, row],
    .cons (.literal 0xffffffffffffffff) .nil
      (.cons (.literal 1) .nil
        (.cons .add (.cons (weaken row maxWire) (.cons oneWire .nil))
          (.cons .add (.cons old (.cons sumWire .nil)) .nil))),
    .cons (newest .head) (.cons (weaken row sumWire) .nil)⟩

private def packetAt (p : Program inputs sigs [word]) (block : Block [word, word] [wordPort]) (guard : Bool) :
    BitVec 64 × BitVec 64 :=
  let entry : Tuple (Val model.value) (dataPorts inputs) :=
    .cons ⟨guard⟩ (.cons (41 : BitVec 64) (.cons (0xffffffffffffffff : BitVec 64) .nil))
  let suffixEntry : Tuple (Val model.value) args :=
    .cons (entry.get p.residual) (p.diamond.denote model entry)
  let values := block.packet.read suffixEntry (block.flow.eval model suffixEntry PUnit.unit)
  (values.get .head, values.get (.tail .head))

theorem wrapping_fold_exposes_right_zero_and_keeps_the_second_packet_value :
    (rewrite (sourceWith 7) x .left).map (fun result => match result with
      | .materialized .right _ p =>
        let ext := withTail p wrappingAdd
        let first := (step? ext).map fun (edit : Edit ext) => (edit.rule, edit.state.block.sigs.length, addCount edit.state.block)
        let final := Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize ext
        some (first, final.rules, final.state.block.packet.addresses,
          packetAt p ext false, packetAt p final.state.block false,
          packetAt p ext true, packetAt p final.state.block true)
      | _ => none) =
      .ok (some (some (.literal, 7, 3), [.literal, .rightZero, .deleteUnused, .deleteUnused],
        [.output 2 0, .output 3 0], (9, 0), (9, 0), (48, 0), (48, 0))) := rfl

/-- A non-add relay provides the actual emitted return as a runtime RHS.
The extra packet field observes the relay independently of the new add. -/
private def literalOnLeft (value : BitVec 64) (past : List (List (Ty Unit)))
    (old : Origin args past wordPort) : TestTail past :=
  let lit : Origin args (past ++ [row]) wordPort := newest .head
  let one : Origin args ((past ++ [row]) ++ [row]) wordPort := newest .head
  let relay : Origin args (((past ++ [row]) ++ [row]) ++ [row]) wordPort := newest .head
  let old := weaken row (weaken row old)
  ⟨[row, row, row, row],
    .cons (.literal value) .nil (.cons (.literal 1) .nil
      (.cons .mul (.cons old (.cons one .nil))
        (.cons .add (.cons (weaken row (weaken row lit)) (.cons relay .nil)) .nil))),
    .cons (newest .head) (.cons (weaken row relay) .nil)⟩

private def orderSummary (value : BitVec 64) :=
  (rewrite (sourceWith 7) x .left).map (fun result => match result with
    | .materialized .right _ p =>
      let ext := withTail p (literalOnLeft value)
      let first := (step? ext).map fun (edit : Edit ext) =>
        (edit.rule, edit.state.block.sigs.length, addCount edit.state.block, leftLiteralCount edit.state.block)
      let final := Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize ext
      let after := final.state.block
      let ordered := (findProducer? after.program after.program.result).map fun (candidate : Producer after.program.dataflow word) =>
        candidate.key.operands.addresses
      some (leftLiteralCount ext, first, final.rules, (step? after).isNone,
        after.packet.addresses, ordered, packetAt p ext false, packetAt p after false,
        packetAt p ext true, packetAt p after true)
    | _ => none)

theorem literal_left_zero_swaps_then_erases_on_the_actual_suffix :
    orderSummary 0 =
      .ok (some (1, some (.literalRight, 7, 3, 0), [.literalRight, .rightZero, .deleteUnused], true,
        [.output 4 0, .output 4 0], some [.output 2 0, .output 3 0], (9, 9), (9, 9), (48, 48), (48, 48))) := rfl

theorem nonzero_literal_moves_right_once_and_stays_there :
    orderSummary 5 =
      .ok (some (1, some (.literalRight, 7, 3, 0), [.literalRight], true,
        [.output 6 0, .output 5 0], some [.output 5 0, .output 3 0], (14, 9), (14, 9), (53, 48), (53, 48))) := rfl

theorem the_diamond_adapter_keeps_the_actual_phi_wires_after_the_swap :
    (rewrite (sourceWith 7) x .left).map (fun result => match result with
      | .materialized .right _ p =>
        let extended := { p with suffix := (withTail p (literalOnLeft 0)).program }
        let target := normalize extended
        some (target.suffix.sigs.length, target.diamond.merge,
          (target.diamond.arms .first).outputs.addresses, (target.diamond.arms .second).outputs.addresses,
          observe target false, observe target true)
      | _ => none) =
      .ok (some (5, ⟨.onFalse⟩, [.output 0 0], [.output 2 0], 9, 48)) := rfl

private def bothLive : Block [word, word] [] :=
  ⟨residualAdd.sigs, residualAdd.dataflow, .cons residualAdd.result .nil⟩

theorem ordinary_live_operands_have_no_eligible_swap :
    step? bothLive = none ∧
      (Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize bothLive).state.block = bothLive :=
  ⟨rfl, rfl⟩

/-- The original inner add already feeds the outer add. Add a second copy
for a subtraction and for the packet's second field. -/
private def repeatedAdd (reversed : Bool) (past : List (List (Ty Unit)))
    (old : Origin args past wordPort) : TestTail past :=
  let capture : Origin args past wordPort := .arg .head
  let phi : Origin args past wordPort := .arg (.tail .head)
  let operands := if reversed then .cons phi (.cons capture .nil) else .cons capture (.cons phi .nil)
  let copy : Origin args (past ++ [row]) wordPort := newest .head
  ⟨[row, row], .cons .add operands
      (.cons .sub (.cons (weaken row old) (.cons copy .nil)) .nil),
    .cons (newest .head) (.cons (weaken row copy) .nil)⟩

private def reuseSummary (reversed : Bool) :=
  (rewrite (sourceWith 7) x .left).map (fun result => match result with
    | .materialized .right _ p =>
      let ext := withTail p (repeatedAdd reversed)
      let final := Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize ext
      let after := final.state.block
      let ordered := (findProducer? after.program after.program.result).map
        fun (candidate : Producer after.program.dataflow word) => candidate.key.operands.addresses
      some (final.rules, after.sigs.length, (step? after).isNone, after.packet.addresses, ordered,
        packetAt p ext false, packetAt p after false, packetAt p ext true, packetAt p after true)
    | _ => none)

theorem exact_add_reuse_shares_a_producer_across_two_observable_consumers :
    reuseSummary false =
      .ok (some ([.reuseAdd], 4, true, [.output 3 0, .output 1 0], some [.output 2 0, .output 1 0],
        (7, 2), (7, 2), (7, 41), (7, 41))) := rfl

theorem reversed_operands_keep_the_later_producer_live_and_distinct :
    reuseSummary true =
      .ok (some ([], 5, true, [.output 4 0, .output 3 0], some [.output 2 0, .output 3 0],
        (7, 2), (7, 2), (7, 41), (7, 41))) := rfl

theorem materialized_diamond_reuse_keeps_predecessor_occurrences :
    (rewrite (sourceWith 7) x .left).map (fun result => match result with
      | .materialized .right _ p =>
        let extended := { p with suffix := (withTail p (repeatedAdd false)).program }
        let target := normalize extended
        some (target.suffix.sigs.length, target.diamond.merge,
          (target.diamond.arms .first).outputs.addresses, (target.diamond.arms .second).outputs.addresses,
          observe target false, observe target true)
      | _ => none) =
      .ok (some (4, ⟨.onFalse⟩, [.output 0 0], [.output 2 0], 7, 7)) := rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery.Regression
