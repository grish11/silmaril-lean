module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (InputWord Program residualAdd)
open AddPhi.Rotate.Pair.Dispatch (Refusal)
open AddPhi.Rotate.Pair.Dispatch.Materialize
open AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay (Request)
open Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay (Block Failure)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word, word]
private abbrev sigs := [[wordPort], [wordPort]]

/-- The right Φ materializes as zero. The left Φ has a live subtraction
on the true occurrence, which is the Region's second predecessor. -/
private def source : AddPhi.Pair.Source inputs sigs where
  shared := .cons (.literal 3) .nil (.cons (.literal 0) .nil .nil)
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

private def x : InputWord inputs := .tail (.tail .head)

private def plan (p : Program inputs sigs [word]) (repeatZero : Bool) : Option (List (Request p)) := do
  let zero ← Cleanup.UnusedZero.leadingZero? p.suffix
  let cut : Request p := ⟨.deleteUnused, zero.origin⟩
  pure ([⟨.idealize, p.suffix.result⟩, cut] ++ if repeatZero then [cut] else [])

private abbrev Attempt := Except Refusal (Option (Except Failure (Program inputs sigs [word])))

private def runDiamond (repeatZero : Bool) : Attempt :=
  (rewrite source x .left).map fun result =>
    match result with
    | .materialized .right _ p => (plan p repeatZero).map (SuffixReplay.rewrite p)
    | _ => none

private def observe {joined : List (ValueSort Unit)} (p : Program inputs sigs joined) (guard : Bool) :
    BitVec 64 :=
  let entry : Tuple (Val model.value) (dataPorts inputs) :=
    .cons ⟨guard⟩ (.cons (41 : BitVec 64) (.cons (0xffffffffffffffff : BitVec 64) .nil))
  p.denote entry

theorem outer_zero_cleanup_replays_on_the_emitted_graph :
    (runDiamond false).map (Option.map (fun result => result.map fun target =>
      (target.suffix, target.diamond.merge, (target.diamond.arms .first).outputs.addresses,
        (target.diamond.arms .second).outputs.addresses, observe target false, observe target true))) =
      .ok (some (.ok (residualAdd, ⟨.onFalse⟩, [.output 0 0], [.output 2 0],
        observe (AddPhi.Rotate.Pair.original source x) false, observe (AddPhi.Rotate.Pair.original source x) true))) ∧
    (observe (AddPhi.Rotate.Pair.original source x) false, observe (AddPhi.Rotate.Pair.original source x) true) =
      (2, 41) := ⟨rfl, rfl⟩

theorem retired_slot_does_not_nominate_the_add_that_shifted_into_it :
    runDiamond true = .ok (some (.error ⟨2, .stale⟩)) := rfl

private def block (packetReadsZero : Bool) : Block [word] [wordPort] where
  sigs := [[wordPort], [wordPort], [wordPort]]
  flow := .cons (.literal 0) .nil
    (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil))
      (.cons .add (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil)) .nil))
  packet := .cons (.output (2 : Fin 3) .head)
    (.cons (if packetReadsZero then .output (0 : Fin 3) .head else .output (1 : Fin 3) .head) .nil)

private def replayPacket (packetReadsZero : Bool) :=
  let p := block packetReadsZero
  let outer := p.packet.get .head
  Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.run p
    [⟨.idealize, outer⟩, ⟨.idealize, outer⟩, ⟨.deleteUnused, .output (0 : Fin 3) .head⟩]

theorem repeated_nomination_follows_redirection_and_checks_every_packet_use :
    (replayPacket false).map (fun state =>
      (state.block.sigs.length, state.block.packet.addresses,
        (state.route (.output (2 : Fin 3) .head)).map (fun wire => wire.address))) =
        .ok (0, [.arg 0, .arg 0], some (.arg 0)) ∧
    replayPacket true = .error ⟨2, .liveUse⟩ := ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Regression
