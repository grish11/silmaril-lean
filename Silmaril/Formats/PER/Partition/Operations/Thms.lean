module

public import Silmaril.Formats.PER.Partition.Operations.Defs
public import Silmaril.Formats.PER.UnionFind.Thms
import Silmaril.Proofs.Formats.PER.PartitionOperations

public section

namespace Silmaril.Formats.PER.Partition

open Silmaril.Semantics

variable {Key : Type}

theorem total_partial (map : TotalMap Key) (cover : ∀ key, (partialOfTotal map key).isSome) :
    totalOfPartial (partialOfTotal map) cover = map := rfl

theorem partial_total (map : PartialMap Key) (cover : ∀ key, (map key).isSome) :
    partialOfTotal (totalOfPartial map cover) = map :=
  funext fun key => Option.some_get (cover key)

theorem total_fibers (map : TotalMap Key) : fibers (partialOfTotal map) = PER.kernel map :=
  PER.ext fun left right => by
    change (∃ label, some (map left) = some label ∧ some (map right) = some label) ↔ map left = map right
    simp [eq_comm]

theorem total_rooted_iff (map : TotalMap Key) : Rooted (partialOfTotal map) ↔ Idempotent map := by
  constructor
  · exact fun h key => Option.some.inj (h (member := key) rfl)
  · intro h key root hit; cases Option.some.inj hit; exact congrArg some (h key)

theorem tabulate_exact [LinearOrder Key] (keys : Finset Key) (lookup : PartialMap Key) :
    (tabulate keys lookup).lookup? = lookup ↔ ∀ key, (lookup key).isSome → key ∈ keys :=
  Proofs.Formats.PERPartitionOperations.tabulate_exact keys lookup

theorem finite_lookup_iff [LinearOrder Key] (lookup : PartialMap Key) :
    (OrderedMap.support lookup).Finite ↔ ∃ labels : FiniteMap Key, finiteLookup labels = lookup :=
  OrderedMap.finite_support_iff lookup

theorem join_left (left right : PER Key) : left ≤ join left right := fun _ _ hit upper => upper.property.1 hit

theorem join_right (left right : PER Key) : right ≤ join left right := fun _ _ hit upper => upper.property.2 hit

theorem join_le_iff {left right upper : PER Key} : join left right ≤ upper ↔ left ≤ upper ∧ right ≤ upper :=
  ⟨fun h => ⟨(join_left left right).trans h, (join_right left right).trans h⟩, fun h _ _ pair => pair ⟨upper, h⟩⟩

theorem union_partition [LinearOrder Key] {state result : UnionFind Key} {left right : Key}
    (hit : state.union left right = some result) : result.partition = join state.partition (identify left right) :=
  Proofs.Formats.PERPartitionOperations.union_join hit

theorem join_comm (left right : PER Key) : join left right = join right left := by
  apply le_antisymm <;> exact join_le_iff.mpr ⟨join_right _ _, join_left _ _⟩

theorem join_idem (relation : PER Key) : join relation relation = relation :=
  le_antisymm (join_le_iff.mpr ⟨le_rfl, le_rfl⟩) (join_left _ _)

theorem join_empty (relation : PER Key) : join relation (PER.empty Key) = relation :=
  le_antisymm (join_le_iff.mpr ⟨le_rfl, fun _ _ h => h.elim⟩) (join_left _ _)

theorem join_dom (left right : PER Key) (key : Key) : (join left right).Dom key ↔ left.Dom key ∨ right.Dom key :=
  Proofs.Formats.PERPartitionOperations.join_dom left right key

theorem le_meet_iff {lower left right : PER Key} : lower ≤ meet left right ↔ lower ≤ left ∧ lower ≤ right :=
  ⟨fun h => ⟨fun _ _ pair => (h pair).1, fun _ _ pair => (h pair).2⟩, fun ⟨hl, hr⟩ _ _ pair => ⟨hl pair, hr pair⟩⟩

theorem meet_dom (left right : PER Key) (key : Key) : (meet left right).Dom key ↔ left.Dom key ∧ right.Dom key := Iff.rfl

theorem meet_comm (left right : PER Key) : meet left right = meet right left := PER.ext fun _ _ => and_comm

theorem meet_idem (relation : PER Key) : meet relation relation = relation :=
  PER.ext fun _ _ => ⟨And.left, fun h => ⟨h, h⟩⟩

theorem meet_universal (relation : PER Key) : meet relation (PER.universal Key) = relation :=
  PER.ext fun _ _ => ⟨And.left, fun h => ⟨h, trivial⟩⟩

theorem join_meet_absorb (left right : PER Key) : join left (meet left right) = left :=
  le_antisymm (join_le_iff.mpr ⟨le_rfl, fun _ _ h => h.1⟩) (join_left _ _)

theorem meet_join_absorb (left right : PER Key) : meet left (join left right) = left :=
  le_antisymm (fun _ _ h => h.1) (le_meet_iff.mpr ⟨le_rfl, join_left _ _⟩)

theorem restrict_entails (relation : PER Key) (selected : Key → Prop) : Entails (relation.restrict selected) relation :=
  fun _ _ h => h.2.2

theorem restrict_dom (relation : PER Key) (selected : Key → Prop) (key : Key) :
    (relation.restrict selected).Dom key ↔ selected key ∧ relation.Dom key :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1, h.2⟩⟩

theorem intersectMaps_partition [LinearOrder Key] (left right : FiniteMap Key) :
    fibers (intersectMaps left right).lookup? = meet (fibers left.lookup?) (fibers right.lookup?) :=
  @canonicalOn_partition _ _ left.keySet _ (meetLabelsDecidable left right)
    (fun key hit => (map_dom_iff_key left key).mp hit.1)

theorem restrictMap_partition [LinearOrder Key] (labels : FiniteMap Key) (selected : Finset Key) :
    fibers (restrictMap labels selected).lookup? = (fibers labels.lookup?).restrict (· ∈ selected) :=
  Proofs.Formats.PERPartitionOperations.restrict_partition labels selected

theorem finite_join [LinearOrder Key] (left right : FiniteMap Key) :
    ∃ labels : FiniteMap Key, fibers labels.lookup? = join (fibers left.lookup?) (fibers right.lookup?) :=
  Proofs.Formats.PERPartitionOperations.finite_join left right

end Silmaril.Formats.PER.Partition
