module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Institution

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF.SwitchAssert (Cfg)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (lower)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution (Profile observe observeCfg)

theorem run_fromTwo_observe {B : Profile} {entrySigs headerSigs : List (List (Diamond.Ty Width))}
    {g : Loop.MLIR.CF.Program B.inputs B.carried B.result entrySigs headerSigs}
    {header : List Header.Pair.Request} {record : First B.inputs B.carried B.result}
    {producer consumer : Nomination} {two : AfterReorder.Second.Emit.Emission B.inputs B.carried B.result}
    {state : State B.inputs two.prepared.intermediate.1 B.carried B.result [two.prepared.consumer.width]}
    {requests : List Nomination} {out : Output B.inputs two.prepared.intermediate.1 B.carried B.result}
    (seed : replay g header [producer, consumer] = .ok (.two record consumer two))
    (initialized : initial? (Step.fromTwo record consumer two) = some state)
    (accepted : run state 2 requests = .ok out) (input : Env B.inputs) :
    observeCfg out.2.cfg input = observe (B := B) (lower g) input := by
  apply Part.ext
  intro outcome
  simp only [observeCfg, observe, Cfg.mem_denotePart_iff, Cfg.embed_run,
    run_fromTwo_run_eq seed initialized accepted]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Institution
