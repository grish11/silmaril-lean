module

public import Silmaril.Formats.Arrow.DateValues.Defs
import Silmaril.Proofs.Formats.Arrow.DateValues.Codec

/-! Ordered slots and exact null counts for the checked DATE buffer adapter. -/

public section

namespace Silmaril.Formats.Arrow.DateValues

open Silmaril.Numeric.Gregorian (CivilDate)

/-- Successful descriptor validation is exactly DATE, the selected unit and little endian. -/
theorem Descriptor.validate_iff (descriptor : Descriptor) (unit : Unit) :
    descriptor.validate unit = .ok () ↔
      descriptor.typeTag = 8 ∧ descriptor.dateUnit = unit.code ∧ descriptor.endianness = 0 := by
  by_cases tag : descriptor.typeTag = 8 <;> by_cases dateUnit : descriptor.dateUnit = unit.code <;>
    simp [Descriptor.validate, tag, dateUnit]

theorem readSlot_iff (unit : Unit) (view : View) (slot : Nat) (date : Option CivilDate) :
    readSlot unit view slot = .ok date ↔ SlotWire unit view slot date :=
  Proofs.Formats.Arrow.DateValues.readSlot_iff unit view slot date

/-- Success is exactly the checked input and its ordered nullable byte observation. -/
theorem decode_iff (limits : Limits) (unit : Unit) (descriptor : Descriptor) (view : View)
    (dates : Column) :
    decode limits unit descriptor view = .ok dates ↔
      check limits unit descriptor view = .ok () ∧ ColumnWire unit view dates :=
  Proofs.Formats.Arrow.DateValues.decode_iff limits unit descriptor view dates

/-- The observed count and null count are exactly those of the checked field node. -/
theorem ColumnWire.counts {unit : Unit} {view : View} {dates : Column}
    (wire : ColumnWire unit view dates) :
    dates.length = view.node.length ∧ dates.countP Option.isNone = view.node.nullCount :=
  ⟨by simpa using wire.1.length_eq.symm, wire.2⟩

/-- An output index observes the corresponding physical slot, including the slice offset. -/
theorem ColumnWire.slot {unit : Unit} {view : View} {dates : Column}
    (wire : ColumnWire unit view dates) (slot : Fin dates.length) :
    SlotWire unit view slot.val (dates.get slot) := by
  have index : slot.val < (List.range view.node.length).length := wire.1.length_eq.symm ▸ slot.isLt
  simpa [List.get_eq_getElem] using wire.1.get index slot.isLt

/-- A null observation comes exactly from an unset validity bit. -/
theorem SlotWire.isNone_iff {unit : Unit} {view : View} {slot : Nat} {date : Option CivilDate}
    (wire : SlotWire unit view slot date) :
    date = none ↔ Body.validAt view.validity (view.start + slot) = some false := by
  obtain ⟨valid, _, bit, _, observed⟩ := wire
  cases valid
  · simpa [bit] using observed
  · obtain ⟨_, _, rfl⟩ := observed; simp [bit]

/-- Record-body slicing follows the checked bitmap and values descriptors. -/
theorem batchView_layout {limits : Limits} {batch : RecordBatch} {body : KBytes} {view : View}
    (arranged : batchView limits batch body = .ok view) :
    ∃ node bitmap data, batch.nodes = [node] ∧ batch.buffers = [bitmap, data] ∧
      node.length = batch.rowCount ∧ BuffersFit body.len 0 [bitmap, data] ∧
      view = ⟨0, node, Body.sliceBuffer body bitmap, Body.sliceBuffer body data⟩ :=
  Proofs.Formats.Arrow.DateValues.batchView_layout arranged

theorem decodeBatch_iff (limits : Limits) (unit : Unit) (descriptor : Descriptor)
    (batch : RecordBatch) (body : KBytes) (dates : Column) :
    decodeBatch limits unit descriptor batch body = .ok dates ↔
      ∃ view, batchView limits batch body = .ok view ∧
        check limits unit descriptor view = .ok () ∧ ColumnWire unit view dates :=
  Proofs.Formats.Arrow.DateValues.decodeBatch_iff limits unit descriptor batch body dates

/-- Successful IPC binding preserves the batch row count and field-node null count. -/
theorem decodeBatch_counts {limits : Limits} {unit : Unit} {descriptor : Descriptor}
    {batch : RecordBatch} {body : KBytes} {dates : Column}
    (decoded : decodeBatch limits unit descriptor batch body = .ok dates) :
    ∃ node, batch.nodes = [node] ∧ dates.length = batch.rowCount ∧
      dates.countP Option.isNone = node.nullCount := by
  obtain ⟨_, arranged, _, wire⟩ := (decodeBatch_iff _ _ _ _ _ _).mp decoded
  obtain ⟨node, _, _, nodes, _, rows, _, rfl⟩ := batchView_layout arranged
  exact ⟨node, nodes, wire.counts.1.trans rows, wire.counts.2⟩

end Silmaril.Formats.Arrow.DateValues
