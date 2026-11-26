module

public import Silmaril.Formats.Arrow.DateValues.Defs

public section

namespace Silmaril.Proofs.Formats.Arrow.DateValues

open Silmaril Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.DateValues
open Silmaril.Numeric.Gregorian (CivilDate)

theorem readSlot_iff (unit : DateValues.Unit) (view : View) (slot : Nat) (date : Option CivilDate) :
    readSlot unit view slot = .ok date ↔ SlotWire unit view slot date := by
  cases bit : Body.validAt view.validity (view.start + slot) with
  | none => simp [readSlot, SlotWire, bit]
  | some valid =>
    cases word : view.values.readLE (unit.width * (view.start + slot)) unit.width with
    | none => simp [readSlot, SlotWire, bit, word]
    | some value =>
      cases valid with
      | false => simp [readSlot, SlotWire, bit, word, pure, Except.pure, eq_comm]
      | true =>
        cases interpreted : unit.toCivil? value <;>
          simp [readSlot, SlotWire, bit, word, interpreted, pure, Except.pure, eq_comm]

private theorem readSlots_iff (unit : DateValues.Unit) (view : View) (slots : List Nat) (dates : DateValues.Column) :
    slots.mapM (readSlot unit view) = .ok dates ↔ List.Forall₂ (SlotWire unit view) slots dates := by
  induction slots generalizing dates with
  | nil => cases dates <;> simp [pure, Except.pure]
  | cons slot slots ih =>
    rw [List.mapM_cons]
    cases first : readSlot unit view slot <;> cases rest : slots.mapM (readSlot unit view) <;>
      cases dates <;> simp [first, rest, ← readSlot_iff, ← ih, Bind.bind, Except.bind, pure, Except.pure]

theorem decode_iff (limits : Limits) (unit : DateValues.Unit) (descriptor : Descriptor) (view : View)
    (dates : DateValues.Column) :
    decode limits unit descriptor view = .ok dates ↔
      check limits unit descriptor view = .ok () ∧ ColumnWire unit view dates := by
  cases checked : check limits unit descriptor view with
  | error error => simp [decode, checked, Bind.bind, Except.bind]
  | ok ready =>
    cases ready
    cases read : (List.range view.node.length).mapM (readSlot unit view) with
    | error error => simp [decode, checked, ColumnWire, ← readSlots_iff, read, Bind.bind, Except.bind]
    | ok result =>
      by_cases count : result.countP Option.isNone = view.node.nullCount
      · simp [decode, checked, ColumnWire, ← readSlots_iff, read, count, Bind.bind,
          Except.bind, pure, Except.pure]
        rintro rfl
        exact count
      · simp [decode, checked, ColumnWire, ← readSlots_iff, read, count, Bind.bind, Except.bind]
        rintro rfl
        exact count

theorem batchView_layout {limits : Limits} {batch : RecordBatch} {body : KBytes} {view : View}
    (arranged : batchView limits batch body = .ok view) :
    ∃ node bitmap data, batch.nodes = [node] ∧ batch.buffers = [bitmap, data] ∧
      node.length = batch.rowCount ∧ BuffersFit body.len 0 [bitmap, data] ∧
      view = ⟨0, node, Body.sliceBuffer body bitmap, Body.sliceBuffer body data⟩ := by
  unfold batchView at arranged
  split at arranged
  · cases arranged
  split at arranged
  · cases arranged
  split at arranged
  · rename_i node bitmap data nodes buffers
    split at arranged
    · rename_i layout
      cases arranged
      exact ⟨node, bitmap, data, nodes, buffers, layout.1, layout.2, rfl⟩
    · cases arranged
  · cases arranged

theorem decodeBatch_iff (limits : Limits) (unit : DateValues.Unit) (descriptor : Descriptor)
    (batch : RecordBatch) (body : KBytes) (dates : DateValues.Column) :
    DateValues.decodeBatch limits unit descriptor batch body = .ok dates ↔
      ∃ view, batchView limits batch body = .ok view ∧
        check limits unit descriptor view = .ok () ∧ ColumnWire unit view dates := by
  cases arranged : batchView limits batch body <;>
    simp [DateValues.decodeBatch, arranged, Bind.bind, Except.bind, decode_iff]

end Silmaril.Proofs.Formats.Arrow.DateValues
