module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Example.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Example.Defs

/-! Audit the earlier refusal and run the admitted embedding suffix. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Example

open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.Loop.SCCP (bankTuple)
open SeaOfNodes.MLIR (Word)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted EntryFacts)
open Semantics.Dataflow (Flat)
open Identification (Refusal checkWrites pushFacts program)
open Identification.Example (old identify lhs rhs original changesAdmission)
open LiftComposition.Example (first second)
open Factorization.Example (finalSignature)
open Composition (thenMap)
open Composition.Example (insertion)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

/-- The earlier two-contraction example passes all structural checks. -/
def previousWriteChecks : Option (Bool × Bool × Bool) := do
  let source ← changesAdmission.toOption
  let body := @Admitted.source _ _ old.bankEq source
  return (checkWrites first body, checkWrites second (program first body), checkWrites (thenMap first second) body)

/-- Read the header continuation fact and true, false, and exit marks
from the drained FIFO assignment. -/
def headerFacts (S : EntrySignature) (p : Program Op S.regs (.data width)) (facts : EntryFacts S.regs) :
    Flat (ULift Bool) × Bool × Bool × Bool :=
  let solved := @SCCP.Worklist.solve _ _ _ _ model p S.bankEq facts
  let header := SCCP.blockFacts model p.header (bankTuple solved.2.1)
  (header.get p.again, decide (SCCP.incomingIndex (.feedback true) ∈ solved.1),
    decide (SCCP.incomingIndex (.feedback false) ∈ solved.1), decide (SCCP.exitIndex ∈ solved.1))

/-- Inspect original, intermediate, and one-shot entry operands and header rows.
The intermediate row is analyzed with the pushed facts even if it refuses. -/
def previousRows : Option (List ((Flat (Word width) × Flat (Word width)) ×
    (Flat (ULift Bool) × Bool × Bool × Bool))) := do
  let source ← changesAdmission.toOption
  let body := @Admitted.source _ _ old.bankEq source
  let facts := @Admitted.facts _ _ old.bankEq source
  let composed := thenMap first second
  let midFacts ← pushFacts first facts
  let finalFacts ← pushFacts composed facts
  return [((facts.get lhs, facts.get rhs), headerFacts old body facts),
    ((midFacts.get (first _ lhs), midFacts.get (first _ rhs)), headerFacts old (program first body) midFacts),
    ((finalFacts.get (composed _ lhs), finalFacts.get (composed _ rhs)),
      headerFacts finalSignature (program composed body) finalFacts)]

def previousOneShotRefusal : Option Refusal := do
  let source ← changesAdmission.toOption
  match Identification.compile (thenMap first second) source with
  | .error reason => some reason
  | .ok _ => none

/-- Repeat the refusal through the suffix that only inserts an unused i16. -/
def embeddingRefusals : Option (Option LiftComposition.Refused × Option Refusal) := do
  let source ← changesAdmission.toOption
  let staged := match LiftComposition.compare identify insertion.portMap source with
    | .error reason => some reason
    | .ok _ => none
  let direct := match Identification.compile (thenMap identify insertion.portMap) source with
    | .error reason => some reason
    | .ok _ => none
  return (staged, direct)

/-- The same suffix succeeds for the guarded program with a known dispatch. -/
def embeddedAccepted : Bool :=
  (original.toOption.bind fun p => (LiftComposition.compare identify insertion.portMap p).toOption).isSome

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Example
