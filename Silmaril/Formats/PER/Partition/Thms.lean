module

public import Silmaril.Formats.PER.Partition.Defs
public import Silmaril.Formats.PER.UnionFind.Defs
import Silmaril.Proofs.Formats.PER.Partition

public section

namespace Silmaril.Formats.PER.Partition

open Silmaril.Semantics

variable {Key : Type} [LinearOrder Key]

theorem canonicalOn_lookup_spec (keys : Finset Key) (relation : PER Key) [DecidableRel relation.rel]
    (covers : ∀ key, relation.Dom key → key ∈ keys) (key root : Key) :
    (canonicalOn keys relation).lookup? key = some root ↔
      relation.rel key root ∧ ∀ other, relation.rel key other → root ≤ other :=
  Proofs.Formats.PERPartition.canonical_lookup_spec keys relation covers key root

theorem canonicalOn_partition (keys : Finset Key) (relation : PER Key) [DecidableRel relation.rel]
    (covers : ∀ key, relation.Dom key → key ∈ keys) : fibers (canonicalOn keys relation).lookup? = relation :=
  Proofs.Formats.PERPartition.canonical_partition keys relation covers

theorem map_dom_iff_key (labels : OrderedMap Key Key) (key : Key) :
    (fibers labels.lookup?).Dom key ↔ key ∈ labels.keySet :=
  (fibers_dom labels.lookup? key).trans (labels.mem_keySet key).symm

theorem normalize_partition (labels : OrderedMap Key Key) :
    fibers (normalize labels).lookup? = fibers labels.lookup? :=
  @canonicalOn_partition Key _ _ _ (labelsDecidable labels.lookup?) fun key => (map_dom_iff_key labels key).mp

theorem normalize_lookup_spec (labels : OrderedMap Key Key) (key root : Key) :
    (normalize labels).lookup? key = some root ↔
      (fibers labels.lookup?).rel key root ∧ ∀ other, (fibers labels.lookup?).rel key other → root ≤ other :=
  @canonicalOn_lookup_spec Key _ _ _ (labelsDecidable labels.lookup?)
    (fun member => (map_dom_iff_key labels member).mp) key root

theorem normalize_eq_iff (left right : OrderedMap Key Key) :
    normalize left = normalize right ↔ fibers left.lookup? = fibers right.lookup? := by
  constructor
  · intro same; rw [← normalize_partition left, ← normalize_partition right, same]
  · exact fun same => OrderedMap.eq_of_lookup fun key => Option.ext fun root => by simp [normalize_lookup_spec, same]

theorem normalize_idem (labels : OrderedMap Key Key) : normalize (normalize labels) = normalize labels :=
  (normalize_eq_iff (normalize labels) labels).mpr (normalize_partition labels)

theorem finite_support_iff (relation : PER Key) :
    ({key | relation.Dom key} : Set Key).Finite ↔
      ∃ labels : OrderedMap Key Key, fibers labels.lookup? = relation :=
  Proofs.Formats.PERPartition.finite_support_iff relation

theorem normalize_rooted (labels : OrderedMap Key Key) : Rooted (normalize labels).lookup? := by
  intro key root hit
  obtain ⟨related, least⟩ := (normalize_lookup_spec labels key root).mp hit
  exact (normalize_lookup_spec labels root root).2 ⟨(fibers labels.lookup?).dom_right related,
    fun _ other => least _ ((fibers labels.lookup?).laws.trans related other)⟩

/-- Recover a rooted state from arbitrary external labels without treating
them as pointers. Its selected roots are the least class members. -/
def toUnionFind (labels : OrderedMap Key Key) : UnionFind Key := ⟨normalize labels, normalize_rooted labels⟩

theorem toUnionFind_partition (labels : OrderedMap Key Key) :
    (toUnionFind labels).partition = fibers labels.lookup? := normalize_partition labels

end Silmaril.Formats.PER.Partition
