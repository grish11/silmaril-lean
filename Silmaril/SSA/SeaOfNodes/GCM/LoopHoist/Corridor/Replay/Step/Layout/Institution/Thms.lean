module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Institution.Correctness

/-! Partial CF observations after checked physical-layout replay. -/

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout

open Silmaril.MLIR.Arith (Env Width)
open Loop.MLIR.CF (Program inputSorts lower)
open Loop.MLIR.CF.Institution (Profile observe observeCfg translateProgram)

variable {B : Profile} {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {header : List Header.Pair.Request} {record : First B.inputs B.carried B.result}
variable {producer consumer : Nomination} {two : AfterReorder.Second.Emit.Emission B.inputs B.carried B.result}
variable {state : State B.inputs two.prepared.intermediate.1 B.carried B.result [two.prepared.consumer.width]}
variable {requests : List Nomination} {out : Output B.inputs two.prepared.intermediate.1 B.carried B.result}

/-- The emitted CFG and the original lowering have the same partial observation
    at every captured input, with no termination hypothesis. -/
theorem run_fromTwo_observe {g : Program B.inputs B.carried B.result entrySigs headerSigs}
    (seed : replay g header [producer, consumer] = .ok (.two record consumer two))
    (initialized : initial? (Step.fromTwo record consumer two) = some state)
    (accepted : run state 2 requests = .ok out) (input : Env B.inputs) :
    observeCfg out.2.cfg input = observe (B := B) (lower g) input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Institution.run_fromTwo_observe
    seed initialized accepted input

/-- Replay on the realized graph can replace the institution's ordinary
    lowering in partial equations and universal termination assertions. -/
theorem run_fromTwo_translate_observe (S : Loop.MLIR.CF.Institution.Signature)
    {g : Loop.Graph S.left.op (inputSorts B.inputs) [.data B.carried] entrySigs headerSigs (.data B.result)}
    (seed : replay (Loop.Institution.mapGraph S.hom g) header [producer, consumer] = .ok (.two record consumer two))
    (initialized : initial? (Step.fromTwo record consumer two) = some state)
    (accepted : run state 2 requests = .ok out) (input : Env B.inputs) :
    observeCfg out.2.cfg input = observe (translateProgram (B := B) S ⟨_, _, _, g⟩ rfl) input :=
  run_fromTwo_observe seed initialized accepted input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout
