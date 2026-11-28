module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Chain.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Chain

/-! Exact coverage and compatibility for checked capture chains. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.CaptureChain

open CategoryTheory
open CarriedAddress.Institution.RuntimeEntry (Entry)
open Memory.Diamond.Institution renaming Signature → EntrySignature

variable {P Q R : EntrySignature} {cells : Nat}

theorem composite_append (left : CaptureChain P Q) (right : CaptureChain Q R) :
    (left.append right).composite = left.composite ≫ right.composite :=
  Proofs.composite_append left right

theorem pullStages_first (chain : CaptureChain P Q) (target : Entry Q.args cells) :
    (chain.pullStages target).first = target.reduct chain.composite :=
  Proofs.pullStages_first chain target

theorem pullStages_last (chain : CaptureChain P Q) (target : Entry Q.args cells) :
    (chain.pullStages target).last = target :=
  Proofs.pullStages_last chain target

theorem pullStages_compatible (chain : CaptureChain P Q) (target : Entry Q.args cells) :
    (chain.pullStages target).Compatible :=
  Proofs.pullStages_compatible chain target

/-- Every compatible chain is determined by its final entry, including the heap. -/
theorem Stages.eq_pullStages {chain : CaptureChain P Q} (stages : Stages cells chain) (edges : stages.Compatible) :
    stages = chain.pullStages stages.last :=
  Proofs.eq_pullStages stages edges

theorem Stages.first_eq_reduct_last {chain : CaptureChain P Q} (stages : Stages cells chain)
    (edges : stages.Compatible) : stages.first = stages.last.reduct chain.composite := by
  rw [stages.eq_pullStages edges, pullStages_first, pullStages_last]

/-- The final tuple alone supplies entries at every stage by typed reduct.
The equivalence also holds when a zero-cell signature cannot admit addresses. -/
theorem admitsStages_iff (chain : CaptureChain P Q) (cells : Nat) :
    (∃ stages : Stages cells chain, stages.Compatible) ↔ admitsInput cells Q.args = true :=
  ⟨fun ⟨stages, _⟩ => (admitsInput_iff cells Q.args).mpr ⟨stages.last.input⟩,
    fun admitted => let ⟨input⟩ := (admitsInput_iff cells Q.args).mp admitted
      ⟨chain.pullStages ⟨input, fun _ => 0⟩, chain.pullStages_compatible _⟩⟩

theorem lift?_sound {chain : CaptureChain P Q} {source : Entry P.args cells} {stages : Stages cells chain}
    (lifted : chain.lift? source = some stages) :
    stages.first = source ∧ stages.Compatible ∧ stages.last.heap = source.heap :=
  Proofs.lift?_sound lifted

theorem lift?_isSome_iff (chain : CaptureChain P Q) (source : Entry P.args cells) :
    (chain.lift? source).isSome = true ↔ InReductImage chain.composite source.input :=
  Proofs.lift?_isSome_iff chain source

theorem compatible_iff_image (chain : CaptureChain P Q) (source : Entry P.args cells) :
    (∃ stages : Stages cells chain, stages.first = source ∧ stages.Compatible) ↔
      InReductImage chain.composite source.input :=
  Proofs.compatible_iff_image chain source

theorem checkCoverage_iff_lift (chain : CaptureChain P Q) (cells : Nat) :
    chain.checkCoverage cells = true ↔ ∀ source : Entry P.args cells, (chain.lift? source).isSome = true :=
  Proofs.checkCoverage_iff_lift chain cells

/-- Coverage decides whether every source entry has a single compatible
chain of lifts at the chosen cell count. -/
theorem checkCoverage_iff_stages (chain : CaptureChain P Q) (cells : Nat) :
    chain.checkCoverage cells = true ↔
      ∀ source : Entry P.args cells, ∃ stages : Stages cells chain, stages.first = source ∧ stages.Compatible :=
  (chain.checkCoverage_iff_lift cells).trans <| forall_congr' fun source =>
    (chain.lift?_isSome_iff source).trans (chain.compatible_iff_image source).symm

theorem diagnose?_isSome_eq (chain : CaptureChain P Q) (cells : Nat) :
    (chain.diagnose? cells).isSome = !chain.checkCoverage cells :=
  diagnoseCoverage?_isSome_eq chain.composite cells

theorem diagnose?_rejects (chain : CaptureChain P Q) {diagnostic : CoverageDiagnostic P Q cells}
    (found : chain.diagnose? cells = some diagnostic) (heap : Heap cells) :
    chain.lift? ⟨diagnostic.input, heap⟩ = none := by
  rw [← Option.isNone_iff_eq_none, ← Option.isSome_eq_false_iff, Bool.eq_false_iff]
  exact fun lifted => CoverageDiagnostic.not_in_image chain.composite (diagnoseCoverage?_valid _ found)
    ((chain.lift?_isSome_iff _).mp lifted)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.CaptureChain
