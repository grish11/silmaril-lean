module

public import Mathlib.Data.Finset.Sort
public import Silmaril.Formats.Dasl.Encode.Map.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.SparseBitmap

open Silmaril.Semantics (OrderedMap)

/-- A layout parameter with one through eight usable bits per byte. -/
abbrev Width := Fin 8

abbrev Offset (width : Width) := Fin (width.val + 1)

abbrev Point (width : Width) := UInt64 × Offset width

abbrev Page (width : Width) := {mask : BitVec (width.val + 1) // mask ≠ 0}

/-- Page identifiers are ordered by their unsigned bit patterns. -/
abbrev pageOrder : LinearOrder UInt64 := LinearOrder.lift' UInt64.toNat (fun _ _ => UInt64.toNat.inj)

attribute [local instance] pageOrder

abbrev Layout (width : Width) := OrderedMap UInt64 (Page width)

variable {width : Width}

instance : DecidableEq (Layout width) := fun left right =>
  decidable_of_iff (left.entries = right.entries) ⟨OrderedMap.ext, congrArg OrderedMap.entries⟩

def maskFor (points : Finset (Point width)) (index : UInt64) : BitVec (width.val + 1) :=
  let flags := (List.finRange (width.val + 1)).map (fun offset => decide ((index, offset) ∈ points))
  (BitVec.ofBoolListLE flags).cast (by simp [flags])

def layoutFor (points : Finset (Point width))
    (nonempty : ∀ index ∈ points.image Prod.fst, maskFor points index ≠ 0) : Layout width :=
  let indices := points.image Prod.fst
  let valid := fun index (hit : index ∈ indices.sort pageOrder.le) =>
    nonempty index ((Finset.mem_sort pageOrder.le).mp hit)
  let entry : ∀ index, maskFor points index ≠ 0 → UInt64 × Page width :=
    fun index proof => (index, ⟨maskFor points index, proof⟩)
  ⟨(indices.sort pageOrder.le).pmap entry valid,
    (Finset.sortedLT_sort indices).pairwise.pmap (f := entry) valid (fun _ _ _ _ ordered => ordered)⟩

def contains (layout : Layout width) (point : Point width) : Bool :=
  ((layout.lookup? point.1).map (fun page => page.val.getLsbD point.2.val)).getD false

def offsets {bits : Nat} (mask : BitVec bits) : List (Fin bits) :=
  (List.finRange bits).filter (fun offset => mask.getLsbD offset.val)

def points (layout : Layout width) : List (Point width) :=
  layout.entries.flatMap (fun entry => (offsets entry.2.val).map (entry.1, ·))

def members (layout : Layout width) : Finset (Point width) := (points layout).toFinset

def pageCount (layout : Layout width) : Nat := layout.entries.length

def cardinality (layout : Layout width) : Nat :=
  (layout.entries.map (fun entry => (offsets entry.2.val).length)).sum

/-- Only usable bits contribute. Duplicate page identifiers contribute by union. -/
def rawPoints (entries : List (UInt64 × UInt8)) : List (Point width) :=
  entries.flatMap (fun (index, byte) => ((List.finRange (width.val + 1)).filter
    (fun offset => byte.toBitVec.getLsbD offset.val)).map (index, ·))

def pageByte (page : Page width) : UInt8 := UInt8.ofNat page.val.toNat

/-- Unlike construction from raw pages, decoding rejects nonzero padding and empty pages. -/
def pageFromByte? (byte : UInt8) : Option (Page width) := do
  if fits : byte.toNat < 2 ^ (width.val + 1) then
    let mask := BitVec.ofNatLT byte.toNat fits
    if nonempty : mask ≠ 0 then some ⟨mask, nonempty⟩ else none
  else none

def singleByte : Encode.TotalCodec UInt8 ByteArray where
  encode byte := ⟨#[byte]⟩
  decode? bytes := if single : bytes.size = 1 then some (bytes[0]'(by omega)) else none
  recovers _ := rfl

end Silmaril.Formats.Dasl.SparseBitmap
