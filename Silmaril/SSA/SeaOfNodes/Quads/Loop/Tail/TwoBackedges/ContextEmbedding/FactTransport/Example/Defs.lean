module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Example.Defs

/-! Exercise conflicts, final unused facts, and the second write check. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Example

open Admission
open SeaOfNodes.MLIR (Word)
open Semantics.Dataflow (Flat)
open Identification (PortMap checkWrites program pushFacts)
open Identification.Example (old new identify original originalProgram contract)
open Weakening.Guarded.Example (captureWidth)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (EntryFacts)
open Composition (thenMap)

/-- The first stage keeps the multiplier at 8. The second identifies it
with the canonical threshold at 7 and gets an empty intersection. -/
def conflictFacts : EntryFacts Noninjective.old.regs :=
  write Noninjective.multiplier (.constant (8 : Word width)) Noninjective.oldFacts

/-- First, staged-final, and one-shot fact success. -/
def conflict : Bool × Bool × Bool :=
  let mid := pushFacts Noninjective.first conflictFacts
  (mid.isSome, (mid.bind (pushFacts Noninjective.second)).isSome,
    (pushFacts Noninjective.composed conflictFacts).isSome)

/-- The final interior i16 capture stays unconstrained after both intersections. -/
def unusedDefault : Option (Flat (Word captureWidth)) :=
  ((pushFacts LiftComposition.Example.first (contract .overdefined)).bind
    (pushFacts LiftComposition.Example.second)).map fun facts => facts.get Factorization.Example.gap

/-- The first map leaves the old rhs slot unused in the intermediate bank.
This suffix identifies that slot with the written output. -/
def unsafeSuffix : PortMap old new := fun sort => fun
  | .tail (.tail (.tail .head)) => .tail (.tail (.tail .head))
  | port => identify sort port

def unsafeWrites : Bool × Bool × Bool :=
  let first := LiftComposition.Example.first
  (checkWrites first originalProgram, checkWrites unsafeSuffix (program first originalProgram),
    checkWrites (thenMap first unsafeSuffix) originalProgram)

/-- The direct map never sees the spare intermediate slot. The staged
compiler still checks every intermediate preimage of a written slot. -/
def unsafeOutcomes : Option Noninjective.Outcomes := do
  let p ← original.toOption
  let first := LiftComposition.Example.first
  return ⟨(Identification.compile first p).map (fun q => selectedSide q.source),
    (LiftComposition.compare first unsafeSuffix p).map (fun q => selectedSide q.staged.source),
    (Identification.compile (thenMap first unsafeSuffix) p).map (fun q => selectedSide q.source)⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Example
