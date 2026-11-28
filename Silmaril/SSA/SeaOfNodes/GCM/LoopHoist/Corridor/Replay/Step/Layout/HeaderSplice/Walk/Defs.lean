module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Defs

/-! # A checked rightward walk for one origin in the current saved header -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk

open Silmaril.MLIR.Arith (Width)
open AfterReorder.Second (savedHeader)

variable {Input extra : List Width} {saved carried result : Width} {origin : Nat}

structure Cursor (state : Layout.State Input saved carried result extra) (origin : Nat) where
  binding : CrossBlock.Kept (Label saved carried result extra)
  checked : CrossBlock.keep? state origin = some binding

def Cursor.check? (state : Layout.State Input saved carried result extra) (origin : Nat) :
    Option (Cursor state origin) :=
  match found : CrossBlock.keep? state origin with
  | none => none
  | some binding => some ⟨binding, found⟩

abbrev Position (Input : List Width) (saved carried result : Width) (extra : List Width) (origin : Nat) :=
  (state : Layout.State Input saved carried result extra) × Cursor state origin

def Position.index (position : Position Input saved carried result extra origin) : Nat :=
  position.2.binding.index

structure Step (source : Position Input saved carried result extra origin) where
  move : HeaderSplice.Move source.1
  emitted : HeaderSplice.emit? source.1 ⟨origin, source.index + 2⟩ = some move
  next : Cursor move.next origin
  advanced : next.binding.index = source.index + 1

def Step.target {source : Position Input saved carried result extra origin} (step : Step source) :
    Position Input saved carried result extra origin :=
  ⟨step.move.next, step.next⟩

/-- Move one position later. Compute the cut before removal in this CFG,
    then verify the original identity's translated position on the emitted CFG. -/
def step? (source : Position Input saved carried result extra origin) : Option (Step source) := do
  match emitted : HeaderSplice.emit? source.1 ⟨origin, source.index + 2⟩ with
  | none => none
  | some move =>
    let next ← Cursor.check? move.next origin
    if advanced : next.binding.index = source.index + 1 then
      some ⟨move, emitted, next, advanced⟩
    else none

inductive Stop (source : Position Input saved carried result extra origin) where
  | limit
  | blocked (checked : step? source = none)

inductive Trace : Position Input saved carried result extra origin → Type where
  | halt {source} (reason : Stop source) : Trace source
  | step {source} (first : Step source) (rest : Trace first.target) : Trace source

/-- The bound counts successful crossings. A failed attempt leaves the last
    accepted CFG and certifies refusal at that position. -/
def visit (source : Position Input saved carried result extra origin) : Nat → Trace source
  | 0 => .halt .limit
  | n + 1 =>
    match checked : step? source with
    | none => .halt (.blocked checked)
    | some first => .step first (visit first.target n)

def Trace.last {source : Position Input saved carried result extra origin} :
    Trace source → Position Input saved carried result extra origin
  | .halt _ => source
  | .step _ rest => rest.last

/-- Actual initial and emitted candidates, in execution order. Each index is a
    cut immediately before the binding in that candidate's own header. -/
def Trace.positions {source : Position Input saved carried result extra origin} :
    Trace source → List (Position Input saved carried result extra origin)
  | .halt _ => [source]
  | .step _ rest => source :: rest.positions

def Trace.stop {source : Position Input saved carried result extra origin} :
    (trace : Trace source) → Stop trace.last
  | .halt reason => reason
  | .step _ rest => rest.stop

def Trace.blocked {source : Position Input saved carried result extra origin} (trace : Trace source) : Bool :=
  match trace.stop with
  | .limit => false
  | .blocked _ => true

structure Walk (state : Layout.State Input saved carried result extra) (origin : Nat) where
  start : Cursor state origin
  trace : Trace ⟨state, start⟩

/-- Refuse unsupported layouts and origins that do not resolve to a live binding. -/
def walk? (state : Layout.State Input saved carried result extra) (origin budget : Nat) :
    Option (Walk state origin) := do
  if Layout.Discovery.supported? state then
    let start ← Cursor.check? state origin
    pure ⟨start, visit ⟨state, start⟩ budget⟩
  else none

structure Ranked (state : Layout.State Input saved carried result extra) (request : Nomination) where
  crossBlock : CrossBlock.Analysis state
  walked : Walk state request.origin

/-- Preserve the certified cross-block depth decision. If it stays in the
    header, use the latest position the checked walk actually visited. -/
def Ranked.selection {state : Layout.State Input saved carried result extra} {request : Nomination}
    (ranked : Ranked state request) : Point (Label saved carried result extra) × Layout.Output Input saved carried result :=
  if ranked.crossBlock.selectedMove?.isSome then (ranked.crossBlock.point, ranked.crossBlock.output)
  else (⟨savedHeader, ranked.walked.trace.last.index⟩, ⟨extra, ranked.walked.trace.last.1⟩)

/-- Compare the checked header walk with a nominated physical preheader cut
    on the original input CFG. -/
def rank? (state : Layout.State Input saved carried result extra) (request : Nomination) (budget : Nat) :
    Option (Ranked state request) := do
  let crossBlock ← CrossBlock.analyze? state request
  let walked ← walk? state request.origin budget
  pure ⟨crossBlock, walked⟩

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk
