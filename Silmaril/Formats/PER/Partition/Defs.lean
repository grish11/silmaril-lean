module

public import Silmaril.Formats.PER.Fibers.Thms
public import Silmaril.Semantics.OrderedMap.Finite.Thms

@[expose] public section

namespace Silmaril.Formats.PER.Partition

open Silmaril.Semantics

variable {Key : Type} [LinearOrder Key]

/-- Pick the least class member in the supplied universe, or fail if no
member is present. The universe need only cover the support, not all of `Key`. -/
def least? (keys : Finset Key) (relation : PER Key) [DecidableRel relation.rel] (key : Key) : Option Key :=
  let members := keys.filter (relation.rel key)
  if present : members.Nonempty then some (members.min' present) else none

def canonicalOn (keys : Finset Key) (relation : PER Key) [DecidableRel relation.rel] : OrderedMap Key Key :=
  OrderedMap.ofLookupOn keys (least? keys relation)

@[instance_reducible] def labelsDecidable (labels : Key → Option Key) : DecidableRel (fibers labels).rel :=
  fun left right =>
    decidable_of_iff ((labels left).isSome ∧ labels left = labels right) ⟨
      fun ⟨present, equal⟩ => by obtain ⟨value, hit⟩ := Option.isSome_iff_exists.mp present; exact ⟨value, hit, equal ▸ hit⟩,
      fun ⟨_, leftHit, rightHit⟩ => ⟨Option.isSome_iff_exists.mpr ⟨_, leftHit⟩, leftHit.trans rightHit.symm⟩⟩

/-- Discard the old choice of labels, retaining the same partial partition. -/
def normalize (labels : OrderedMap Key Key) : OrderedMap Key Key :=
  @canonicalOn Key _ labels.keySet (fibers labels.lookup?) (labelsDecidable labels.lookup?)

end Silmaril.Formats.PER.Partition
