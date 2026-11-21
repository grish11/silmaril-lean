module

public import Silmaril.Formats.Dasl.SparseIntSet.Defs
import Silmaril.Proofs.Formats.Dasl.SparseIntSet

public section

namespace Silmaril.Formats.Dasl.SparseIntSet

attribute [local instance] signedOrder

@[simp] theorem members_ofFinset (values : Finset Int64) : members (ofFinset values) = values := by
  simp [members, ofFinset, Semantics.OrderedMap.keys, List.map_map, Function.comp_def]

@[simp] theorem ofFinset_members (layout : Layout) : ofFinset (members layout) = layout :=
  Proofs.Formats.Dasl.SparseIntSet.ofFinset_members layout

def equiv : Layout ≃ Finset Int64 := ⟨members, ofFinset, ofFinset_members, members_ofFinset⟩

@[simp] theorem members_normalize (values : List Int64) : members (normalize values) = values.toFinset :=
  members_ofFinset _

theorem normalize_eq_iff (left right : List Int64) :
    normalize left = normalize right ↔ ∀ value, value ∈ left ↔ value ∈ right := by
  rw [← equiv.injective.eq_iff]; change members (normalize left) = members (normalize right) ↔ _
  simp [Finset.ext_iff]

theorem contains_iff (layout : Layout) (value : Int64) : contains layout value = true ↔ value ∈ members layout := by
  simp [contains, members]

theorem cardinality_eq (layout : Layout) : cardinality layout = (members layout).card :=
  (List.toFinset_card_of_nodup layout.keys_nodup).symm

end Silmaril.Formats.Dasl.SparseIntSet
