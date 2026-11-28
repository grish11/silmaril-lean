module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Defs

/-! # Check and emit one move on an existing saved CFG -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Loop.MLIR.CF (Program TargetOp)

variable {Input extra : List Width} {saved carried result : Width}

structure State (Input : List Width) (saved carried result : Width) (extra : List Width) where
  cfg : Cfg TargetOp (Label saved carried result extra) Input [result]
  origins : List Nat
  slots : Saved.Slots (extra ++ [saved])

structure Emission (Input : List Width) (saved carried result : Width) (extra : List Width) where
  index : Nat
  candidate : AfterReorder.Second.Candidate Input saved carried result extra
  next : State Input saved carried result (candidate.width :: extra)

/-- Reuse an actual two-move replay result as input to the shared step. -/
def fromTwo (first : First Input carried result) (second : Nomination)
    (moved : AfterReorder.Second.Emit.Emission Input carried result) :
    State Input moved.prepared.intermediate.1 carried result [moved.prepared.consumer.width] :=
  let snapshot : Snapshot Input carried result := .two first second moved
  ⟨moved.cfg, snapshot.origins, snapshot.savedSlots⟩

/-- The supported cut follows the contiguous leading saves. Check the
current binding, captured operands and exact use occurrences at that cut. -/
def emit (state : State Input saved carried result extra) (request : Nomination) :
    Except Reason (Emission Input saved carried result extra) :=
  let widths := extra ++ [saved]
  if request.cut = widths.length then
    let attempt : Option (Emission Input saved carried result extra) := do
      let index ← state.origins.idxOf? request.origin
      let candidate ← AfterReorder.Second.findCaptured? index 0 (Saved.origins widths) (state.cfg.block .header)
      if AfterReorder.Second.checkConsumer state.cfg candidate then
        let cfg ← AfterReorder.Second.Emit.emitAt? state.cfg index candidate.op candidate.inputs
        pure ⟨index, candidate, ⟨cfg, state.origins.eraseIdx index, .cons request.origin state.slots⟩⟩
      else none
    match attempt with
    | some moved => .ok moved
    | none => .error .rejected
  else .error (.wrongCut widths.length)

abbrev Output (Input : List Width) (saved carried result : Width) :=
  (extra : List Width) × State Input saved carried result extra

/-- Replay a suffix starting at the supplied nomination position.
An error reports the first refused request and carries no CFG. -/
def run : {extra : List Width} → State Input saved carried result extra → Nat →
    List Nomination → Except Refusal (Output Input saved carried result)
  | extra, state, _, [] => .ok ⟨extra, state⟩
  | _, state, position, request :: rest =>
    match emit state request with
    | .error reason => .error (.nomination position request reason)
    | .ok moved => run moved.next (position + 1) rest

inductive Result (Input : List Width) (carried result : Width) where
  | initial (snapshot : Snapshot Input carried result)
  | extended (saved : Width) (out : Output Input saved carried result)

def Result.Labels : Result Input carried result → List Width → Type
  | .initial snapshot => snapshot.Labels
  | .extended saved out => Label saved carried result out.1

def Result.cfg : (out : Result Input carried result) → Cfg TargetOp out.Labels Input [result]
  | .initial snapshot => snapshot.cfg
  | .extended _ out => out.2.cfg

def Result.origins : Result Input carried result → List Nat
  | .initial snapshot => snapshot.origins
  | .extended _ out => out.2.origins

/-- Replay the initial checked moves with the original driver. A longer
plan continues from its exact two-save CFG and reports absolute positions. -/
def replayAll {entrySigs headerSigs : List (List (Diamond.Ty Width))}
    (g : Program Input carried result entrySigs headerSigs) (header : List Header.Pair.Request) :
    List Nomination → Except Refusal (Result Input carried result)
  | producer :: consumer :: request :: rest =>
    match Replay.replay g header [producer, consumer] with
    | .ok (.two first second moved) =>
      (run (fromTwo first second moved) 2 (request :: rest)).map (.extended _)
    | .ok _ => .error .header
    | .error reason => .error reason
  | nominations => (Replay.replay g header nominations).map .initial

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step
