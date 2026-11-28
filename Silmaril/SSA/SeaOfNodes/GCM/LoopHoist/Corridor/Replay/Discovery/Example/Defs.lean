module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Example.Defs

/-! # Discover a dependent chain and stop at a latch-dependent binding -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Loop.MLIR.CF (TargetOp evalOp)
open AfterReorder.Second (checkPrefixCut findCaptured?)
open Corridor.Example (word Inputs input)
open AfterReorder.Second.Example (first)

def chain : Except Refusal (Plan Inputs word word) :=
  discover Step.Example.loop first.header

def immutableSecond : Except Refusal (Plan Inputs word word) :=
  discover (Step.Example.loopWith true false) first.header

def immutableLater : Except Refusal (Plan Inputs word word) :=
  discover (Step.Example.loopWith false true) first.header

def varying : Except Refusal (Plan Inputs word word) :=
  discover (AfterReorder.Second.Example.loop true) first.header

def unsaved : Except Refusal (Plan Inputs word word) :=
  discover (Corridor.Example.loop true) []

/-- Observe the chosen origin/cut pairs, surviving header order, next candidate,
and outcomes at fuel three through five. -/
def observe (search : Except Refusal (Plan Inputs word word)) :
    Except Refusal (List (Nat × Nat) × List Nat × Option Nomination × List (Option Nat)) :=
  search.map fun plan =>
    (plan.requests.map (fun request => (request.origin, request.cut)), plan.output.origins, next? plan.output,
      [3, 4, 5].map fun fuel => (plan.output.cfg.run evalOp fuel (input 2 10 1)).map (fun env => (env.get .here).toNat))

/-- Report the earliest operand cut, all operand-available cuts, and the
cuts passing the full ordinary and Φ use check, on the current CFG. -/
def observePrefix {saved : Width} {extra : List Width}
    (cfg : Cfg TargetOp (LoopHoist.Label saved word word extra) Inputs [word]) (origins : List Nat)
    (origin : Nat) : Option (Nat × List Nat × List Nat) := do
  let index ← origins.idxOf? origin
  let candidate ← findCaptured? index 0 (Saved.origins (extra ++ [saved])) (cfg.block .header)
  let cuts := List.range ((extra ++ [saved]).length + 2)
  pure (candidate.earliestCut, cuts.filter candidate.operandCut?, cuts.filter (checkPrefixCut cfg candidate))

def immutableInterval : Option (Nat × List Nat × List Nat) := do
  let .ok (.one record) := replay (Step.Example.loopWith true false) first.header [⟨1, 0⟩] | none
  observePrefix record.output.2 record.origins 2

def savedInterval : Option (Nat × List Nat × List Nat) := do
  let .ok (.two record request move) := replay Step.Example.loopWithOlderSave first.header [⟨1, 0⟩, ⟨2, 1⟩] | none
  let state := Step.fromTwo record request move
  observePrefix state.cfg state.origins 5

/-- Both the latch and an unhoisted header prerequisite fail operand capture. -/
def rejectedIntervals : Bool :=
  match replay (AfterReorder.Second.Example.loop true) first.header [⟨1, 0⟩],
      replay Step.Example.loop first.header [⟨1, 0⟩] with
  | .ok (.one latch), .ok (.one localRead) =>
    (observePrefix latch.output.2 latch.origins 2).isNone &&
      (observePrefix localRead.output.2 localRead.origins 5).isNone
  | _, _ => false

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example
