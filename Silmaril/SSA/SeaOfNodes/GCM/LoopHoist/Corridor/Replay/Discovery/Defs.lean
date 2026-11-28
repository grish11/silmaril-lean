module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Defs

/-! # Discover checked nominations on the current single-latch CFG -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery

open Silmaril.MLIR.Arith (Width)
open Loop.MLIR.CF (Program lower)
open Header.Sequence (State)

variable {Input extra : List Width} {saved carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

/-- Visit original identities in their current header order. Keep the
nomination together with the exact result of its successful check. -/
def choose? {α : Type} (origins : List Nat) (cut : Nat) (tryMove : Nomination → Except Reason α) :
    Option (Nomination × α) :=
  origins.findSome? fun origin =>
    let request : Nomination := ⟨origin, cut⟩
    (tryMove request).toOption.map fun out => (request, out)

def firstMove? (state : State Input carried result) :=
  choose? state.origins 0 (Replay.first? state)

def secondMove? (first : First Input carried result) :=
  choose? first.origins 1 (Replay.second? first)

def laterMove? (state : Step.State Input saved carried result extra) :=
  choose? state.origins (extra ++ [saved]).length (Step.emit state)

/-- Ask whether the current emitted CFG has another move in the profile. -/
def next? : Step.Result Input carried result → Option Nomination
  | .initial (.zero state) => (firstMove? state).map Prod.fst
  | .initial (.one first) => (secondMove? first).map Prod.fst
  | .initial (.two first second two) => (laterMove? (Step.fromTwo first second two)).map Prod.fst
  | .extended _ out => (laterMove? out.2).map Prod.fst

def headerOperations : Step.Result Input carried result → List Header.Earlier.Operation
  | .initial snapshot => snapshot.headerOperations
  | .extended _ out => Header.Earlier.operations (out.2.cfg.block .header)

/-- Failure of every nomination in the current replay phase, including
requests for origins or cuts outside the enumerated inventory. -/
def Exhausted : Step.Result Input carried result → Prop
  | .initial (.zero state) => ∀ request, ∃ reason, Replay.first? state request = .error reason
  | .initial (.one first) => ∀ request, ∃ reason, Replay.second? first request = .error reason
  | .initial (.two first second two) =>
    ∀ request, ∃ reason, Step.emit (Step.fromTwo first second two) request = .error reason
  | .extended _ out => ∀ request, ∃ reason, Step.emit out.2 request = .error reason

structure Suffix (Input : List Width) (saved carried result : Width) where
  requests : List Nomination
  output : Step.Output Input saved carried result

/-- Recheck the remaining header after each successful emit. The budget
counts unsaved identities and drops by one for each accepted nomination. -/
def collect : {extra : List Width} → Step.State Input saved carried result extra → Nat →
    Suffix Input saved carried result
  | extra, state, 0 => ⟨[], ⟨extra, state⟩⟩
  | extra, state, fuel + 1 =>
    match laterMove? state with
    | none => ⟨[], ⟨extra, state⟩⟩
    | some (request, moved) =>
      let rest := collect moved.next fuel
      ⟨request :: rest.requests, rest.output⟩

structure Plan (Input : List Width) (carried result : Width) where
  requests : List Nomination
  output : Step.Result Input carried result

/-- Keep the two-hoist result in its original replay representation
when the continuation is empty. -/
def finish (producer consumer : Nomination) (first : First Input carried result)
    (two : AfterReorder.Second.Emit.Emission Input carried result)
    (suffix : Suffix Input two.prepared.intermediate.1 carried result) : Plan Input carried result :=
  match suffix.requests with
  | [] => ⟨[producer, consumer], .initial (.two first consumer two)⟩
  | request :: rest => ⟨producer :: consumer :: request :: rest, .extended _ suffix.output⟩

/-- Discover a deterministic plan after the caller's checked header
reordering. The first two phases use their existing cuts and emitters. -/
def discover (g : Program Input carried result entrySigs headerSigs)
    (header : List Header.Pair.Request) : Except Refusal (Plan Input carried result) :=
  match Header.Sequence.run? (Header.Sequence.initial (lower g)) header with
  | none => .error .header
  | some state =>
    match firstMove? state with
    | none => .ok ⟨[], .initial (.zero state)⟩
    | some (producer, first) =>
      match secondMove? first with
      | none => .ok ⟨[producer], .initial (.one first)⟩
      | some (consumer, two) =>
        let state := Step.fromTwo first consumer two
        .ok (finish producer consumer first two (collect state state.origins.length))

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery
