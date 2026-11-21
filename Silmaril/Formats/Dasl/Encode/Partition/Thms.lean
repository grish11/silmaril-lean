module

public import Silmaril.Formats.Dasl.Encode.Partition.Defs
public import Silmaril.Formats.PER.Partition.Thms
import Silmaril.Proofs.Formats.Dasl.EncodePartition

public section

namespace Silmaril.Formats.Dasl.Encode.Partition

open Silmaril.Semantics

variable {Key Name Ref Target : Type} [LinearOrder Key]

theorem group_member_iff (labels : OrderedMap Key Key) (key label : Key) :
    (∃ members, (label, members) ∈ (group labels).entries ∧ key ∈ members) ↔ labels.lookup? key = some label :=
  Proofs.Formats.Dasl.EncodePartition.group_member labels key label

theorem ungroup?_spec (groups : ClassMembers Key) (labels : OrderedMap Key Key) :
    ungroup? groups = some labels ↔ group labels = groups :=
  Proofs.Formats.Dasl.EncodePartition.ungroup?_spec groups labels

def classMembersLayout : TotalCodec (OrderedMap Key Key) (ClassMembers Key) :=
  ⟨group, ungroup?, fun labels => (ungroup?_spec (group labels) labels).mpr rfl⟩

/-- A sorted table of explicit finite member arrays, with one row per class. -/
def classMembers (key : TotalCodec Key (Tree Ref Name)) :
    TotalCodec (OrderedMap Key Key) (Tree Ref Name) :=
  classMembersLayout.then (pairMap key (finiteSet key))

theorem decodeCanonical (codec : TotalCodec (OrderedMap Key Key) Target) (labels : OrderedMap Key Key) :
    decodePartition codec (encodeCanonical codec labels) = some (PER.fibers labels.lookup?) := by
  simp [decodePartition?, TotalCodec.partial, encodeCanonical, codec.recovers, PER.Partition.normalize_partition]

theorem decodeCanonical? (codec : PartialCodec (OrderedMap Key Key) Target)
    {labels : OrderedMap Key Key} {repr : Target} (hit : encodeCanonical? codec labels = some repr) :
    decodePartition? codec repr = some (PER.fibers labels.lookup?) := by
  simp [decodePartition?, codec.recovers hit, PER.Partition.normalize_partition]

theorem represented_iff (codec : TotalCodec (OrderedMap Key Key) Target) (relation : PER Key) :
    (∃ repr, decodePartition codec repr = some relation) ↔ ({key | relation.Dom key} : Set Key).Finite := by
  rw [PER.Partition.finite_support_iff]
  exact ⟨fun ⟨_, hit⟩ => let ⟨labels, _, h⟩ := Option.map_eq_some_iff.mp hit; ⟨labels, h⟩,
    fun ⟨labels, h⟩ => ⟨encodeCanonical codec labels, h ▸ decodeCanonical codec labels⟩⟩

theorem encodeCanonical_eq_iff (codec : TotalCodec (OrderedMap Key Key) Target) (left right : OrderedMap Key Key) :
    encodeCanonical codec left = encodeCanonical codec right ↔
      (PER.fibers left.lookup?).classes = (PER.fibers right.lookup?).classes :=
  ⟨fun same => PER.classes_eq_iff.mpr ((PER.Partition.normalize_eq_iff left right).mp (codec.injective same)),
   fun same => congrArg codec.encode ((PER.Partition.normalize_eq_iff left right).mpr (PER.classes_eq_iff.mp same))⟩

theorem encodeCanonical?_eq_iff (codec : PartialCodec (OrderedMap Key Key) Target)
    {left right : OrderedMap Key Key} {first second : Target}
    (hl : encodeCanonical? codec left = some first) (hr : encodeCanonical? codec right = some second) :
    first = second ↔ (PER.fibers left.lookup?).classes = (PER.fibers right.lookup?).classes := by
  constructor
  · intro same; exact PER.classes_eq_iff.mpr ((PER.Partition.normalize_eq_iff left right).mp
      (Option.some.inj ((codec.recovers hl).symm.trans (same ▸ codec.recovers hr))))
  · intro same; exact Option.some.inj (hl.symm.trans
      (congrArg codec.encode? ((PER.Partition.normalize_eq_iff left right).mpr (PER.classes_eq_iff.mp same)) |>.trans hr))

end Silmaril.Formats.Dasl.Encode.Partition
