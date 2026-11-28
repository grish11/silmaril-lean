module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Example.Defs

/-! Diagnose the spare-slot collision on the actual first compiler's output. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Example

open Identification (PortMap checkWrites program)
open Identification.Example (old aliasesWrite original originalProgram)
open LiftComposition.Example (first second)
open FactTransport.Example (unsafeSuffix)
open Composition (thenMap)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted)

/-- Report occurrence, intermediate writer, intermediate alias and final slot. -/
def unsafeDiagnostic : Option (Nat × Nat × Nat × Nat) := do
  let input ← original.toOption
  let intermediate ← (Identification.compile first input).toOption
  let collision ← diagnose first unsafeSuffix (@Admitted.source _ _ old.bankEq intermediate.source)
  return (collision.occurrence.val, slot collision.written, slot collision.other,
    slot (unsafeSuffix _ collision.written))

/-- The same first stage followed by a read-only merge has no extra collision. -/
def readOnlyDiagnostic : Option Bool := do
  let input ← original.toOption
  let intermediate ← (Identification.compile first input).toOption
  return (diagnose first second (@Admitted.source _ _ old.bankEq intermediate.source)).isSome

/-- An alias wholly inside the first image is caught by both write checks.
Report first, second and direct write checks, then diagnostic presence. -/
def withinImageChecks : Bool × Bool × Bool × Bool :=
  let identity : PortMap old old := fun _ port => port
  let intermediate := program identity originalProgram
  (checkWrites identity originalProgram, checkWrites aliasesWrite intermediate,
    checkWrites (thenMap identity aliasesWrite) originalProgram,
    (diagnose identity aliasesWrite intermediate).isSome)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Example
