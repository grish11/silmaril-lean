module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission

open Example (writeChecks summary outcomes invalidCases second)
open Identification (program checkWrites)
open Identification.Example (old changesAdmission originalProgram contract)
open LiftComposition.Example (first)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted EntryFacts)
open Reindex.Guarded.Institution (AdmittedAt)

#guard writeChecks == some (true, true, true)
#guard summary == some (.constant ⟨false⟩, .constant ⟨true⟩, [true, false, false, true], 9, 0)
#guard outcomes == some (.error (.checker .neitherMarked), .error (.checker .neitherMarked))
#guard invalidCases == some (.error .aliasedWrite, .error .incompatibleFacts)

/-- On a raw seed with a varying selector, the same inspector reports both
marks. The checked capture compiler starts from an admitted seed instead. -/
private def twoLiveFacts : EntryFacts old.regs :=
  write (.tail .head) .overdefined (contract .overdefined)

example : (match inspect old originalProgram twoLiveFacts with
    | .error refused => some refused.reason
    | .ok () => none) = some .bothMarked := rfl

example (seed : AdmittedAt old width) (original : changesAdmission = .ok seed) :
    checkWrites first (@Admitted.source _ _ old.bankEq seed) = true ∧
    checkWrites second (program first (@Admitted.source _ _ old.bankEq seed)) = true := by
  have checks := congrArg (fun c => c.toOption.map fun seed =>
    let source := @Admitted.source _ _ old.bankEq seed
    (checkWrites first source, checkWrites second (program first source), checkWrites (Composition.thenMap first second) source))
    original
  have expected : writeChecks = some (true, true, true) := rfl
  change writeChecks = some _ at checks
  rw [expected] at checks
  exact ⟨congrArg Prod.fst (Option.some.inj checks).symm, congrArg (fun t => t.2.1) (Option.some.inj checks).symm⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission
