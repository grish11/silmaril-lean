module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective.Checked

/-! A checked first admission and a refused final admission for a write-safe noninjective suffix. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective

open Identification (pushFacts)
open Reindex.Guarded.Institution (AdmittedAt Generated)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)

/-- The suffix identifies two distinct intermediate word ports. -/
theorem suffix_identifies :
    first _ seed ≠ first _ multiplier ∧ second _ (first _ seed) = second _ (first _ multiplier) :=
  Proofs.suffix_identifies

theorem writeChecks_exact : writeChecks = (true, true, true) :=
  Proofs.writeChecks_exact

/-- Both final routes reach the same successful fact intersection. -/
theorem intersections_exact :
    pushFacts first oldFacts = some middleFacts ∧
    pushFacts second middleFacts = some finalFacts ∧
    pushFacts composed oldFacts = some finalFacts :=
  Proofs.intersections_exact

theorem rows_exact :
    rows = some [⟨.overdefined, .overdefined, .overdefined, .overdefined, [true, true, false, true]⟩,
      ⟨.overdefined, .constant 7, .overdefined, .overdefined, [true, true, false, true]⟩,
      ⟨.constant 1, .constant 7, .constant 7, .constant ⟨false⟩, [true, false, false, true]⟩,
      ⟨.constant 1, .constant 7, .constant 7, .constant ⟨false⟩, [true, false, false, true]⟩] :=
  Proofs.rows_exact

theorem outcomes_exact :
    outcomes = some ⟨.ok true, .error (.second (.checker .neitherMarked)), .error (.checker .neitherMarked)⟩ :=
  Proofs.outcomes_exact

/-- The first compiler emits actual artifacts. The second and one-shot
compilers both reach FIFO and refuse because neither feedback is marked. -/
theorem compiler_differential :
    ∃ (source : AdmittedAt old width) (intermediate : Generated middle width),
      original = .ok source ∧
      Identification.compile first source = .ok intermediate ∧
      selectedSide intermediate.source = true ∧
      Identification.compile second intermediate.source = .error (.checker .neitherMarked) ∧
      LiftComposition.compare first second source = .error (.second (.checker .neitherMarked)) ∧
      Identification.compile composed source = .error (.checker .neitherMarked) :=
  Proofs.compiler_differential

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective
