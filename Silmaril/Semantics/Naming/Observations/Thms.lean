module

public import Silmaril.Semantics.Naming.Observations.Defs
public import Silmaril.Semantics.Naming.Thms
import Silmaril.Proofs.Semantics.Naming.Observations

public section

namespace Silmaril.Semantics.Naming

variable {Root Witness Name Obj Blob : Type}

theorem collect_subset_iff {language : Relation Root Witness} {observe : Root → Witness → Relation Name Obj}
    {rel : Relation Name Obj} :
    Subset (collect language observe) rel ↔ ∀ ⦃root witness⦄, language root witness → Subset (observe root witness) rel :=
  ⟨fun incl _ _ hit _ _ witnessed => incl ⟨_, _, hit, witnessed⟩,
    fun incl _ _ ⟨_, _, hit, witnessed⟩ => incl hit witnessed⟩

namespace Stores

theorem Subset.refl (store : Stores Name Obj Blob) : store.Subset store :=
  ⟨fun _ _ hit => hit, fun _ _ hit => hit⟩

theorem Subset.trans {first second third : Stores Name Obj Blob}
    (left : first.Subset second) (right : second.Subset third) : first.Subset third :=
  ⟨fun _ _ hit => right.1 (left.1 hit), fun _ _ hit => right.2 (left.2 hit)⟩

theorem Subset.antisymm {left right : Stores Name Obj Blob} (first : left.Subset right)
    (second : right.Subset left) : left = right := Proofs.Semantics.Naming.store_subset_antisymm first second

theorem subset_union_left (left right : Stores Name Obj Blob) : left.Subset (left.union right) :=
  ⟨fun _ _ hit => Or.inl hit, fun _ _ hit => Or.inl hit⟩

theorem subset_union_right (left right : Stores Name Obj Blob) : right.Subset (left.union right) :=
  ⟨fun _ _ hit => Or.inr hit, fun _ _ hit => Or.inr hit⟩

theorem union_subset {left right ambient : Stores Name Obj Blob} (first : left.Subset ambient)
    (second : right.Subset ambient) : (left.union right).Subset ambient :=
  ⟨fun _ _ hit => hit.elim (first.1 ·) (second.1 ·), fun _ _ hit => hit.elim (first.2 ·) (second.2 ·)⟩

theorem mergeCompatible_iff {left right : Stores Name Obj Blob} :
    left.MergeCompatible right ↔ ∃ ambient, left.Subset ambient ∧ right.Subset ambient ∧ ambient.Binding :=
  ⟨fun bound => ⟨left.union right, subset_union_left left right, subset_union_right left right, bound⟩,
    fun ⟨_, first, second, bound⟩ => bound.subset (union_subset first second)⟩

/-- The observations form the least relation that includes every witness's contribution. -/
theorem collect_subset_iff {language : Relation Root Witness} {observe : Root → Witness → Stores Name Obj Blob}
    {store : Stores Name Obj Blob} :
    (collect language observe).Subset store ↔
      ∀ ⦃root witness⦄, language root witness → (observe root witness).Subset store :=
  ⟨fun incl _ _ hit => ⟨Naming.collect_subset_iff.mp incl.1 hit, Naming.collect_subset_iff.mp incl.2 hit⟩,
    fun incl => ⟨Naming.collect_subset_iff.mpr fun _ _ hit => (incl hit).1,
      Naming.collect_subset_iff.mpr fun _ _ hit => (incl hit).2⟩⟩

theorem collect_mono {left right : Relation Root Witness} (incl : Naming.Subset left right)
    (observe : Root → Witness → Stores Name Obj Blob) :
    (collect left observe).Subset (collect right observe) :=
  collect_subset_iff.mpr fun _ _ hit => collect_subset_iff.mp (Subset.refl (collect right observe)) (incl hit)

end Stores
end Silmaril.Semantics.Naming
