module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission

open Identification (program)
open Identification.Example (originalProgram output rhs)
open LiftComposition.Example (first second)
open FactTransport.Example (unsafeSuffix unsafeOutcomes)

private def preheaderConflict : Conflict (program first originalProgram) :=
  ⟨⟨0, by decide⟩, rhs⟩

/-- The first write to output is reported, even though true feedback also writes to it. -/
example : diagnose first unsafeSuffix (program first originalProgram) = some preheaderConflict :=
  rfl

example : preheaderConflict.written = output := rfl

example : preheaderConflict.Valid first unsafeSuffix :=
  diagnose_sound first unsafeSuffix rfl

example : diagnose first second (program first originalProgram) = none := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
example : Example.unsafeDiagnostic = some (0, 4, 3, 3) := rfl

example : Example.withinImageChecks = (true, false, false, false) := rfl

#guard unsafeOutcomes == some ⟨.ok true, .error (.second .aliasedWrite), .ok true⟩
#guard Example.readOnlyDiagnostic == some false
#guard LiftComposition.Example.run 65535 true ==
  some ((some 99, some 99), (some 99, some 99), (some 99, some 99))
#guard LiftComposition.Example.run 0 false ==
  some ((some 14, some 14), (some 14, some 14), (some 14, some 14))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission
