module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Defs

/-! # Discover a decreasing sequence of ranked hoists on the current saved CFG -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery

open Silmaril.MLIR.Arith (Width)

variable {Input : List Width} {saved carried result : Width}

/-- The real ranker selected the preheader for this live origin. -/
structure Hoist (source : Layout.Output Input saved carried result) (origin : Nat) where
  choice : Sequence.Choice source ⟨origin, 0⟩
  move : Layout.Move source.2
  selected : choice.ranked.crossBlock.selectedMove? = some move

/-- Give the ranker a zero crossing budget. Admit only an actual selected hoist. -/
def hoist? (source : Layout.Output Input saved carried result) (origin : Nat) : Option (Hoist source origin) :=
  match checked : PreheaderSearch.rank? source.2 origin 0 with
  | none => none
  | some ranked =>
    match selected : ranked.crossBlock.selectedMove? with
    | none => none
    | some move => some ⟨⟨ranked, checked⟩, move, selected⟩

/-- Scan the surviving original identities in their current header order. -/
def choose? (source : Layout.Output Input saved carried result) : Option ((origin : Nat) × Hoist source origin) :=
  source.2.reference.origins.findSome? fun origin =>
    (hoist? source origin).map fun chosen => ⟨origin, chosen⟩

structure Plan (source : Layout.Output Input saved carried result) where
  requests : List Sequence.Request
  trace : Sequence.Trace source requests

def Plan.output {source : Layout.Output Input saved carried result} (plan : Plan source) :
    Layout.Output Input saved carried result :=
  plan.trace.output

/-- Recompute the entire admitted choice on each actual selected layout. -/
def collect (source : Layout.Output Input saved carried result) : Nat → Plan source
  | 0 => ⟨[], .done⟩
  | budget + 1 =>
    match choose? source with
    | none => ⟨[], .done⟩
    | some ⟨origin, hoist⟩ =>
      let rest := collect hoist.choice.ranked.selection.2 budget
      ⟨⟨origin, 0⟩ :: rest.requests, .step hoist.choice rest.trace⟩

/-- Validate the initial CFG shape and bound the schedule by its inventory.
    An admitted plan can have zero requests. -/
def schedule? (source : Layout.Output Input saved carried result) : Option (Plan source) :=
  if Layout.Discovery.supported? source.2
  then some (collect source source.2.reference.origins.length)
  else none

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery
