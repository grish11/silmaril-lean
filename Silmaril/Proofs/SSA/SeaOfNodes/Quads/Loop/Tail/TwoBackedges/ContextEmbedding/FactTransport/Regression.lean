module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective.Thms
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport

open Admission
open Identification (pushFacts)
open Example (conflictFacts conflict unusedDefault unsafeWrites unsafeOutcomes)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)
open Reindex.Guarded.Institution (AdmittedAt Generated)

example : pushFacts Noninjective.composed conflictFacts = none := rfl

example : (pushFacts Noninjective.first conflictFacts).isSome = true ∧
    (pushFacts Noninjective.first conflictFacts).bind (pushFacts Noninjective.second) = none :=
  ⟨rfl, (pushFacts_comp _ _ _).symm.trans (show pushFacts Noninjective.composed conflictFacts = none from rfl)⟩

example : unusedDefault = some .overdefined := rfl

#guard conflict == (true, false, false)
#guard LiftComposition.Example.compared.isSome
#guard LiftComposition.Example.run 65535 true ==
  some ((some 99, some 99), (some 99, some 99), (some 99, some 99))
#guard LiftComposition.Example.run 0 false ==
  some ((some 14, some 14), (some 14, some 14), (some 14, some 14))

example (pair : LiftComposition.Compared LiftComposition.Example.first LiftComposition.Example.second width) :
    pair.staged = pair.direct :=
  compared_eq pair

/-- #4748 passes the second write check, so the final FIFO refusal is the
same in both calls despite the successful first compiler. -/
example (p : AdmittedAt Noninjective.old width) (mid : Generated Noninjective.middle width)
    (seeded : Noninjective.original = .ok p)
    (firstOk : Identification.compile Noninjective.first p = .ok mid) :
    Identification.compile Noninjective.second mid.source = Identification.compile Noninjective.composed p := by
  apply second_compile_eq _ _ _ _ firstOk
  rw [Identification.compile_source _ _ firstOk, (Identification.admit_fields _ _ p seeded).1]
  exact congrArg (fun checks => checks.2.1) Noninjective.writeChecks_exact

example : unsafeWrites = (true, false, true) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
example : unsafeOutcomes = some ⟨.ok true, .error (.second .aliasedWrite), .ok true⟩ := rfl

#guard unsafeOutcomes == some ⟨.ok true, .error (.second .aliasedWrite), .ok true⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport
