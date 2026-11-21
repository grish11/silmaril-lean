module

public import Silmaril.Formats.Dasl.SparseRangeSet.Defs
import Silmaril.Proofs.Formats.Dasl.SparseRangeSet

public section

namespace Silmaril.Formats.Dasl.SparseRangeSet

/-- Normalize arbitrary interval order, overlaps and adjacency without enumerating keys. -/
def normalize (ranges : List Interval) : Layout :=
  ⟨mergeRanges ranges, Proofs.Formats.Dasl.SparseRangeSet.merge_separated ranges⟩

@[simp] theorem covers_normalize (ranges : List Interval) (point : Int) :
    Covers (normalize ranges).ranges point ↔ Covers ranges point :=
  Proofs.Formats.Dasl.SparseRangeSet.covers_merge ranges point

theorem eq_of_covers {left right : Layout} (same : ∀ point, Covers left.ranges point ↔ Covers right.ranges point) :
    left = right := Layout.ext (Proofs.Formats.Dasl.SparseRangeSet.eq_of_covers left.separated right.separated same)

theorem normalize_eq_iff (left right : List Interval) :
    normalize left = normalize right ↔ ∀ point, Covers left point ↔ Covers right point := by
  simp only [← covers_normalize left, ← covers_normalize right]
  exact ⟨fun equal _ => equal ▸ Iff.rfl, eq_of_covers⟩

theorem mem_members (layout : Layout) (key : Int64) : key ∈ members layout ↔ Covers layout.ranges key.toInt :=
  Proofs.Formats.Dasl.SparseRangeSet.mem_ranges layout.ranges key

theorem contains_iff (layout : Layout) (key : Int64) : contains layout key = true ↔ key ∈ members layout := by
  simp [contains, mem_members, List.any_eq_true, Covers]

theorem cardinality_eq (layout : Layout) : cardinality layout = (members layout).card :=
  Proofs.Formats.Dasl.SparseRangeSet.card_ranges layout.separated

theorem members_injective : Function.Injective members := by
  intro left right equal
  apply eq_of_covers
  intro point
  simp [Proofs.Formats.Dasl.SparseRangeSet.covers_iff_exists_member, equal]

attribute [local instance] SparseIntSet.signedOrder

def ofFinset (keys : Finset Int64) : Layout :=
  normalize ((keys.sort SparseIntSet.signedOrder.le).map Interval.singleton)

@[simp] theorem members_ofFinset (keys : Finset Int64) : members (ofFinset keys) = keys := by
  ext key
  simp [ofFinset, mem_members, Proofs.Formats.Dasl.SparseRangeSet.covers_singletons]

/-- The inverse may enumerate a finite set; normalization of interval inputs does not. -/
def equiv : Layout ≃ Finset Int64 :=
  ⟨members, ofFinset, fun layout => members_injective (members_ofFinset (members layout)), members_ofFinset⟩

end Silmaril.Formats.Dasl.SparseRangeSet
