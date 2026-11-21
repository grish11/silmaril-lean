module

public import Silmaril.Formats.Dasl.SparseBitmap.Defs
import Silmaril.Proofs.Formats.Dasl.SparseBitmap

public section

namespace Silmaril.Formats.Dasl.SparseBitmap

variable {width : Width}

attribute [local instance] pageOrder

def ofFinset (keys : Finset (Point width)) : Layout width :=
  layoutFor keys (Proofs.Formats.Dasl.SparseBitmap.maskFor_nonempty keys)

@[simp] theorem members_ofFinset (keys : Finset (Point width)) : members (ofFinset keys) = keys :=
  Proofs.Formats.Dasl.SparseBitmap.members_layoutFor keys _

theorem ext_members {left right : Layout width} (same : members left = members right) : left = right :=
  Proofs.Formats.Dasl.SparseBitmap.ext_members same

def equiv : Layout width ≃ Finset (Point width) :=
  ⟨members, ofFinset, fun layout => ext_members (members_ofFinset (members layout)), members_ofFinset⟩

def normalize (keys : List (Point width)) : Layout width := ofFinset keys.toFinset

def normalizePages (entries : List (UInt64 × UInt8)) : Layout width := normalize (rawPoints entries)

@[simp] theorem mem_normalize (keys : List (Point width)) (point : Point width) :
    point ∈ members (normalize keys) ↔ point ∈ keys := by simp [normalize]

theorem normalizePages_eq_iff (left right : List (UInt64 × UInt8)) :
    normalizePages (width := width) left = normalizePages right ↔
      ∀ point : Point width, point ∈ rawPoints left ↔ point ∈ rawPoints right := by
  rw [← equiv.injective.eq_iff, Finset.ext_iff]
  simp [equiv, normalizePages]

theorem contains_iff (layout : Layout width) (point : Point width) :
    contains layout point = true ↔ point ∈ members layout :=
  Proofs.Formats.Dasl.SparseBitmap.contains_iff layout point

theorem cardinality_eq (layout : Layout width) : cardinality layout = (members layout).card :=
  Proofs.Formats.Dasl.SparseBitmap.cardinality_eq layout

def pageCodec : Encode.TotalCodec (Page width) UInt8 :=
  ⟨pageByte, pageFromByte?, Proofs.Formats.Dasl.SparseBitmap.pageByte_recovers⟩

/-- A sorted list of `[page index, one byte]` pairs with nonzero usable masks. -/
def codec {Name : Type} : Encode.TotalCodec (Layout width) (Shallow Name) :=
  Encode.pairMap Encode.bits (pageCodec.then (singleByte.then Encode.bytes))

end Silmaril.Formats.Dasl.SparseBitmap
