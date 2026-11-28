module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Chain.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Defs

/-! A three-map replay whose actual second compiler refuses before the suffix is tried. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.CaptureChain.Example

open Admission.Noninjective (old middle finalSignature body oldFacts)
open SeaOfNodes.MLIR (Word)
open Semantics.Dataflow (Flat)
open Identification (PortMap)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width word)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted admit)
open Reindex.Guarded.Institution (AdmittedAt)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

/-- A read-only i8 slot with a fact of 8, unused by every source body. -/
abbrev withSpare (S : EntrySignature) : EntrySignature := { regs := word :: S.regs }

def keepSpare {S T : EntrySignature} (map : PortMap S T) : PortMap (withSpare S) (withSpare T) :=
  fun sort => fun
    | .head => .head
    | .tail port => .tail (map sort port)

def original : Except SCCP.Dispatch.Refusal (AdmittedAt (withSpare old) width) :=
  @admit _ _ (withSpare old).bankEq (Weakening.program word body)
    (.cons (.constant (8 : Word width)) oldFacts)

def prefixChain : CaptureChain (withSpare old) (withSpare finalSignature) :=
  .cons (keepSpare Admission.Noninjective.first) (.cons (keepSpare Admission.Noninjective.second) (.nil _))

abbrev withPredicate : EntrySignature := { regs := .predicate :: (withSpare finalSignature).regs }

def compatible : CaptureChain (withSpare old) withPredicate :=
  prefixChain.append (.cons (T := withPredicate) (fun _ port => .tail port) (.nil _))

/-- The suffix tries to intersect the spare 8 with the shared read-only 7. -/
def conflictSuffix : PortMap (withSpare finalSignature) finalSignature :=
  fun _ => fun
    | .head => .tail (.tail .head)
    | .tail port => port

def conflict : CaptureChain (withSpare old) finalSignature :=
  prefixChain.append (.cons conflictSuffix (.nil _))

/-- A different suffix aliases the spare with writable scratch. -/
def aliasSuffix : PortMap (withSpare finalSignature) finalSignature :=
  fun _ => fun
    | .head => .tail (.tail (.tail .head))
    | .tail port => port

def aliasing : CaptureChain (withSpare old) finalSignature :=
  prefixChain.append (.cons aliasSuffix (.nil _))

/-- Exercise the last-artifact path with two successful compiler calls. -/
def successful : CaptureChain (withSpare old) (withSpare middle) :=
  .cons (keepSpare Admission.Noninjective.first) (.cons (fun _ port => port) (.nil (withSpare middle)))

def lastSelection : Option Bool := do
  let seed ← original.toOption
  let artifact ← (successful.run seed).lastArtifact
  return selectedSide artifact.source

structure Summary where
  allWrites : Bool
  firstFailure : Option (Nat × Identification.Refusal)
  direct : Except Identification.Refusal Bool
  deriving DecidableEq, Repr

def summarize {T : EntrySignature} (chain : CaptureChain (withSpare old) T) : Option Summary := do
  let seed ← original.toOption
  let code := @Admitted.source _ _ (withSpare old).bankEq seed
  return ⟨chain.checkAllWrites code, (chain.run seed).firstFailure,
    (Identification.compile chain.composite seed).map (fun out => selectedSide out.source)⟩

/-- Display the first artifact's selected side and the refused second row.
The mark order is entry, true feedback, false feedback, exit. -/
def stoppedRow : Option (Bool × Flat (ULift Bool) × List Bool × Nat × Nat) := do
  let seed ← original.toOption
  match compatible.run seed with
  | .passed emitted _ (.stopped failed) =>
    match failed.detail with
    | .fifo row =>
      some (selectedSide emitted.source, row.continuation,
        [decide (SCCP.incomingIndex .entry ∈ row.run.state.1),
         decide (SCCP.incomingIndex (.feedback true) ∈ row.run.state.1),
         decide (SCCP.incomingIndex (.feedback false) ∈ row.run.state.1),
         decide (SCCP.exitIndex ∈ row.run.state.1)],
        row.run.visits.length, row.run.pending.length)
    | _ => none
  | _ => none

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.CaptureChain.Example
