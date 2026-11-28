module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Example.Defs

/-! Two write-safe read-only contractions with a refused first FIFO. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Example

open Semantics.Dataflow (Flat)
open Identification (PortMap checkWrites program)
open Identification.Example (old new changesAdmission identify original conflicting aliasesWrite)
open LiftComposition.Example (first)
open Composition (thenMap)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted)

/-- After the first identification has made both guard operands use lhs,
this suffix maps the spare rhs slot to lhs and removes it from the bank. -/
def second : PortMap old new := identify

def writeChecks : Option (Bool × Bool × Bool) := do
  let seed ← changesAdmission.toOption
  let code := @Admitted.source _ _ old.bankEq seed
  return (checkWrites first code, checkWrites second (program first code),
    checkWrites (thenMap first second) code)

def row : Option (RefusedRow old width) := do
  let seed ← changesAdmission.toOption
  match diagnose first seed with
  | .error (.fifo observed) => some observed
  | _ => none

/-- The two Boolean facts and marks in entry, true, false, exit order,
followed by the actual visit count and pending queue length. -/
def summary : Option (Flat (ULift Bool) × Flat (ULift Bool) × List Bool × Nat × Nat) :=
  row.map fun observed =>
    (observed.continuation, observed.selector,
      [decide (SCCP.incomingIndex .entry ∈ observed.run.state.1),
        decide (SCCP.incomingIndex (.feedback true) ∈ observed.run.state.1),
        decide (SCCP.incomingIndex (.feedback false) ∈ observed.run.state.1),
        decide (SCCP.exitIndex ∈ observed.run.state.1)],
      observed.run.visits.length, observed.run.pending.length)

def outcomes : Option (Except Identification.Refusal Unit × Except Identification.Refusal Unit) := do
  let seed ← changesAdmission.toOption
  return ((Identification.compile first seed).map (fun _ => ()),
    (Identification.compile (thenMap first second) seed).map (fun _ => ()))

def invalidCases : Option (Except Identification.Refusal Unit × Except Identification.Refusal Unit) := do
  let good ← original.toOption
  let inconsistent ← conflicting.toOption
  return ((diagnose aliasesWrite good).mapError Refusal.reason,
    (diagnose identify inconsistent).mapError Refusal.reason)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Example
