module

public import Silmaril.Formats.Arrow.DateValues.Thms
import Silmaril.Formats.Arrow.Layout.Thms
import Silmaril.Prelude.Bytes.Equiv.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.DateFile

open Silmaril.Formats.Arrow

private theorem validAt_congr {left right : KBytes} (wfLeft : left.wf = true)
    (wfRight : right.wf = true) (same : left ≈ right) (slot : Nat) :
    Body.validAt left slot = Body.validAt right slot := by
  simp [Body.validAt, KBytes.len_eq_of_equiv wfLeft wfRight same,
    KBytes.get?_congr wfLeft wfRight same]

/-- Two successful DATE body decodes with the same descriptors and octets
have identical slots, independently of the backing byte tree. -/
theorem sameDecodedBody {limits : Limits} {unit : DateValues.Unit}
    {descriptor : DateValues.Descriptor} {batch : RecordBatch} {left right : KBytes}
    {xs ys : DateValues.Column} (wfLeft : left.wf = true) (wfRight : right.wf = true)
    (same : left.toList = right.toList)
    (decodedLeft : DateValues.decodeBatch limits unit descriptor batch left = .ok xs)
    (decodedRight : DateValues.decodeBatch limits unit descriptor batch right = .ok ys) : xs = ys := by
  obtain ⟨viewLeft, layoutLeft, _, wireLeft⟩ :=
    (DateValues.decodeBatch_iff _ _ _ _ _ _).mp decodedLeft
  obtain ⟨viewRight, layoutRight, _, wireRight⟩ :=
    (DateValues.decodeBatch_iff _ _ _ _ _ _).mp decodedRight
  obtain ⟨node, bitmap, data, nodes, buffers, _, fitsLeft, rfl⟩ :=
    DateValues.batchView_layout layoutLeft
  obtain ⟨otherNode, otherBitmap, otherData, otherNodes, otherBuffers, _, fitsRight, rfl⟩ :=
    DateValues.batchView_layout layoutRight
  rw [nodes] at otherNodes
  rw [buffers] at otherBuffers
  obtain rfl : node = otherNode := by simpa using otherNodes
  obtain ⟨rfl, rfl⟩ : bitmap = otherBitmap ∧ data = otherData := by simpa using otherBuffers
  have bitmapLeft := (fitsLeft.mem_fits (buffer := bitmap) (by simp)).2.2
  have bitmapRight := (fitsRight.mem_fits (buffer := bitmap) (by simp)).2.2
  have dataLeft := (fitsLeft.mem_fits (buffer := data) (by simp)).2.2
  have dataRight := (fitsRight.mem_fits (buffer := data) (by simp)).2.2
  have bitmapSame := KBytes.slice_congr wfLeft wfRight same bitmapLeft
  have dataSame := KBytes.slice_congr wfLeft wfRight same dataLeft
  apply List.ext_getElem (wireLeft.counts.1.trans wireRight.counts.1.symm)
  intro i leftIndex rightIndex
  have atLeft := (DateValues.readSlot_iff _ _ _ _).mpr (wireLeft.slot ⟨i, leftIndex⟩)
  have atRight := (DateValues.readSlot_iff _ _ _ _).mpr (wireRight.slot ⟨i, rightIndex⟩)
  simp only [List.get_eq_getElem] at atLeft atRight
  rw [← Except.ok.injEq, ← atLeft, ← atRight]
  simp [DateValues.readSlot, Body.sliceBuffer,
    validAt_congr (KBytes.wf_slice _ _ _ wfLeft bitmapLeft)
      (KBytes.wf_slice _ _ _ wfRight bitmapRight) bitmapSame,
    KBytes.readLE_congr (KBytes.wf_slice _ _ _ wfLeft dataLeft)
      (KBytes.wf_slice _ _ _ wfRight dataRight) dataSame]

end Silmaril.Proofs.Formats.Arrow.DateFile
