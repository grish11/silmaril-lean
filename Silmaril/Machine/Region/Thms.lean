module

public import Silmaril.Machine.Region.Defs

@[expose] public section
namespace Silmaril.Machine.Region

theorem omitted_data (code : BinaryObject) (memory : Nat → UInt8) :
    (LoadedImage.mk code none).DataCompatible memory := by
  intro source h
  cases h

theorem supplied_data (code : BinaryObject) (source : ByteSource) (memory : Nat → UInt8) :
    (LoadedImage.mk code (some source)).DataCompatible memory ↔
      ∀ n byte, source.read n = some byte → memory n = byte := by
  simp [LoadedImage.DataCompatible]

theorem translate_single (m : Mapping) (l : Label) (h : m.code.Contains l) :
    translate [m] l = some (m.fileOffset + (l.offset - m.code.range.start)) := by
  simp [translate, owners, h]

theorem supportLabels_singleton (s : Segment) (l : Label) :
    supportLabels {s} l ↔ s.Contains l := by simp [supportLabels]
end Silmaril.Machine.Region
