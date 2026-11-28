module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Chain.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.CaptureChain.Proofs

open CategoryTheory
open CarriedAddress.Institution.RuntimeEntry (Entry)
open Memory.Diamond.Institution (reduct reduct_id reduct_comp)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature} {cells : Nat}

theorem composite_append (left : CaptureChain P Q) (right : CaptureChain Q R) :
    (left.append right).composite = left.composite ≫ right.composite := by
  induction left with
  | nil => exact (Category.id_comp _).symm
  | cons head tail ih =>
    change head ≫ (tail.append right).composite = (head ≫ tail.composite) ≫ right.composite
    rw [ih, Category.assoc]

theorem pullStages_last (chain : CaptureChain P Q) (target : Entry Q.args cells) :
    (chain.pullStages target).last = target := by
  induction chain with
  | nil => rfl
  | cons head tail ih => exact ih target

private theorem pullStages_first_model (chain : CaptureChain P Q) (target : Entry Q.args cells) :
    (chain.pullStages target).first.model = reduct chain.composite target.model := by
  induction chain with
  | nil => exact (reduct_id _).symm
  | cons head tail ih =>
    change reduct head (tail.pullStages target).first.model = reduct (head ≫ tail.composite) target.model
    rw [ih target, reduct_comp]

private theorem pullStages_first_heap (chain : CaptureChain P Q) (target : Entry Q.args cells) :
    (chain.pullStages target).first.heap = target.heap := by
  induction chain with
  | nil => rfl
  | cons head tail ih => exact ih target

private theorem entry_eq_of_model_eq_of_heap_eq {left right : Entry P.args cells}
    (model : left.model (P := P) = right.model) (heap : left.heap = right.heap) : left = right := by
  cases left
  cases right
  simp only [Entry.model, EntryModel.mk.injEq, heq_eq_eq, true_and] at model
  rw [Entry.mk.injEq]
  exact ⟨model, heap⟩

theorem pullStages_first (chain : CaptureChain P Q) (target : Entry Q.args cells) :
    (chain.pullStages target).first = target.reduct chain.composite :=
  entry_eq_of_model_eq_of_heap_eq (P := P) (pullStages_first_model chain target) (pullStages_first_heap chain target)

theorem pullStages_compatible (chain : CaptureChain P Q) (target : Entry Q.args cells) :
    (chain.pullStages target).Compatible := by
  induction chain with
  | nil => trivial
  | cons head tail ih => exact ⟨rfl, ih target⟩

theorem eq_pullStages {chain : CaptureChain P Q} (stages : Stages cells chain) (edges : stages.Compatible) :
    stages = chain.pullStages stages.last := by
  induction stages with
  | nil => rfl
  | @cons P Q R tail head entry stages ih =>
    obtain ⟨edge, rest⟩ := edges
    change Stages.cons (head := head) entry stages =
      Stages.cons ((tail.pullStages stages.last).first.reduct head) (tail.pullStages stages.last)
    rw [← ih rest, edge]

theorem lift?_sound {chain : CaptureChain P Q} {source : Entry P.args cells} {stages : Stages cells chain}
    (lifted : chain.lift? source = some stages) :
    stages.first = source ∧ stages.Compatible ∧ stages.last.heap = source.heap := by
  obtain ⟨input, checked, rfl⟩ := Option.map_eq_some_iff.mp lifted
  let target : Entry Q.args cells := ⟨input, source.heap⟩
  refine ⟨?_, pullStages_compatible chain target, congrArg Entry.heap (pullStages_last chain target)⟩
  rw [pullStages_first chain target]
  exact entry_eq_of_model_eq_of_heap_eq (P := P) (liftInput?_sound chain.composite checked) rfl

theorem compatible_iff_image (chain : CaptureChain P Q) (source : Entry P.args cells) :
    (∃ stages : Stages cells chain, stages.first = source ∧ stages.Compatible) ↔
      InReductImage chain.composite source.input := by
  constructor
  · rintro ⟨stages, first, edges⟩
    have pulled : stages.last.reduct chain.composite = source :=
      (pullStages_first chain stages.last).symm.trans ((congrArg Stages.first (eq_pullStages stages edges)).symm.trans first)
    exact ⟨stages.last.input, congrArg (Entry.model (P := P)) pulled⟩
  · rintro ⟨input, pulled⟩
    let target : Entry Q.args cells := ⟨input, source.heap⟩
    refine ⟨chain.pullStages target, ?_, pullStages_compatible chain target⟩
    rw [pullStages_first]
    exact entry_eq_of_model_eq_of_heap_eq (P := P) pulled rfl

theorem lift?_isSome_iff (chain : CaptureChain P Q) (source : Entry P.args cells) :
    (chain.lift? source).isSome = true ↔ InReductImage chain.composite source.input := by
  simpa only [CaptureChain.lift?, Option.isSome_map] using liftInput?_isSome_iff chain.composite source.input

theorem checkCoverage_iff_lift (chain : CaptureChain P Q) (cells : Nat) :
    chain.checkCoverage cells = true ↔ ∀ source : Entry P.args cells, (chain.lift? source).isSome = true := by
  refine (ReductImage.checkCoverage_iff chain.composite cells).trans ⟨?_, ?_⟩
  · exact fun covers source => (lift?_isSome_iff chain source).mpr (covers source.input)
  · exact fun all input => (lift?_isSome_iff chain ⟨input, fun _ => 0⟩).mp (all ⟨input, fun _ => 0⟩)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.CaptureChain.Proofs
