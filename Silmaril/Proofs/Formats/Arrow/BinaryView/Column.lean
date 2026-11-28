module

public import Silmaril.Formats.Arrow.BinaryView.Column.Defs
import Silmaril.Formats.Arrow.BinaryView.Thms
import Init.Data.List.Monadic

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.BinaryView.Column

open Silmaril.Formats
open Silmaril.Formats.Arrow (FieldNode)
open Silmaril.Formats.Arrow.BinaryView.Column

theorem checkBuffers_iff (limits : Limits) (node : FieldNode) (nullable : Bool) (input : Buffers) :
    checkBuffers limits node nullable input = .ok () ↔ BuffersFit limits node nullable input := by
  by_cases rows : node.length ≤ limits.rows
  · by_cases count : input.payload.data.size ≤ limits.dataBuffers
    · by_cases bytes : input.byteCount ≤ limits.bufferBytes
      · by_cases source : input.validity.wf = true ∧ input.payload.views.wf = true ∧
          input.payload.data.all (·.wf) = true
        · by_cases bitmap : Arrow.Body.BitmapExtent input.validity node.length
          · by_cases views : 16 * node.length ≤ input.payload.views.len
            · by_cases nulls : node.nullCount ≤ node.length ∧
                (nullable = true ∨ node.nullCount = 0)
              all_goals simp [checkBuffers, BuffersFit, rows, count, bytes, source, bitmap, views, nulls]
            · simp [checkBuffers, BuffersFit, rows, count, bytes, source, bitmap, views]
          · simp [checkBuffers, BuffersFit, rows, count, bytes, source, bitmap]
        · have rejected : checkBuffers limits node nullable input = .error .malformedSource := by
            simp only [checkBuffers, rows, count, bytes, not_true, ite_false, ite_eq_left source]
          have impossible : ¬ BuffersFit limits node nullable input := fun fits => source fits.2.2.2.1
          simp [rejected, impossible]
      · simp [checkBuffers, BuffersFit, rows, count, bytes]
    · simp [checkBuffers, BuffersFit, rows, count]
  · simp [checkBuffers, BuffersFit, rows]

private theorem readSlot_iff (input : Buffers) (index maxValueBytes : Nat) (value : Option KBytes) :
    readSlot input index maxValueBytes = .ok value ↔ SlotWire input index maxValueBytes value := by
  cases valid : Arrow.Body.validAt input.validity index with
  | none => cases value <;> simp [readSlot, SlotWire, valid]
  | some bit =>
    cases bit with
    | false => cases value <;> simp [readSlot, SlotWire, valid]
    | true =>
      cases read : Arrow.BinaryView.readBinary input.payload index maxValueBytes with
      | error cause =>
        cases value <;> simp [readSlot, SlotWire, valid, read, Except.map, Except.mapError,
          ← Arrow.BinaryView.readBinary_iff]
      | ok bytes =>
        cases value <;> simp [readSlot, SlotWire, valid, read, Except.map, Except.mapError,
          ← Arrow.BinaryView.readBinary_iff]

private theorem readSlots_iff (input : Buffers) (maxValueBytes : Nat)
    (indices : List Nat) (values : List (Option KBytes)) :
    indices.mapM (fun index => readSlot input index maxValueBytes) = .ok values ↔
      SlotsWire input maxValueBytes indices values := by
  induction indices generalizing values with
  | nil => cases values <;> simp [SlotsWire, pure, Except.pure]
  | cons index rest ih =>
    cases first : readSlot input index maxValueBytes with
    | error cause =>
      cases values <;>
        simp [List.mapM_cons, SlotsWire, first, ← readSlot_iff, bind, Except.bind]
    | ok slot =>
      cases tail : rest.mapM (fun index => readSlot input index maxValueBytes) with
      | error cause =>
        cases values <;>
          simp [List.mapM_cons, SlotsWire, first, tail, ← readSlot_iff, ← ih, bind, Except.bind]
      | ok slots =>
        cases values <;>
          simp [List.mapM_cons, SlotsWire, first, tail, ← readSlot_iff, ← ih, bind, Except.bind,
            pure, Except.pure]

theorem readBinary_iff (limits : Limits) (node : FieldNode) (nullable : Bool) (input : Buffers)
    (values : List (Option KBytes)) :
    readBinary limits node nullable input = .ok values ↔ Wire limits node nullable input values := by
  cases checked : checkBuffers limits node nullable input with
  | error cause =>
    simp [readBinary, Wire, ← checkBuffers_iff, checked, bind, Except.bind]
  | ok success =>
    cases success
    cases checkedSlots : (List.range node.length).mapM
        (fun index => readSlot input index limits.valueBytes) with
    | error cause =>
      simp [readBinary, Wire, ← checkBuffers_iff, ← readSlots_iff, checked, checkedSlots,
        bind, Except.bind]
    | ok slots =>
      by_cases same : slots = values
      · subst values
        by_cases nulls : slots.countP Option.isNone = node.nullCount
        · by_cases budget : valueByteCount slots ≤ limits.outputBytes
          all_goals simp [readBinary, Wire, ← checkBuffers_iff, ← readSlots_iff, checked,
            checkedSlots, bind, Except.bind, nulls, budget]
        · simp [readBinary, Wire, ← checkBuffers_iff, ← readSlots_iff, checked,
            checkedSlots, bind, Except.bind, nulls]
      · simp [readBinary, Wire, ← checkBuffers_iff, ← readSlots_iff, checked, checkedSlots,
          same, bind, Except.bind]
        split <;> (try split) <;> simp_all

private theorem slots_length {input : Buffers} {maxValueBytes : Nat} {indices : List Nat}
    {values : List (Option KBytes)} (wire : SlotsWire input maxValueBytes indices values) :
    values.length = indices.length := by
  induction indices generalizing values with
  | nil => cases values <;> simp_all [SlotsWire]
  | cons index rest ih =>
    cases values with
    | nil => exact False.elim wire
    | cons value values => simp [ih wire.2]

theorem readBinary_bounds {limits : Limits} {node : FieldNode} {nullable : Bool} {input : Buffers}
    {values : List (Option KBytes)} (read : readBinary limits node nullable input = .ok values) :
    BuffersFit limits node nullable input ∧ values.length = node.length ∧
      values.countP Option.isNone = node.nullCount ∧ valueByteCount values ≤ limits.outputBytes := by
  obtain ⟨fits, wire, nulls, bytes⟩ := (readBinary_iff _ _ _ _ _).1 read
  exact ⟨fits, (slots_length wire).trans List.length_range, nulls, bytes⟩

theorem readUtf8_iff (limits : Limits) (node : FieldNode) (nullable : Bool) (input : Buffers)
    (values : List (Option String)) :
    readUtf8 limits node nullable input = .ok values ↔
      ∃ slots, Wire limits node nullable input slots ∧
        slots.mapM (·.mapM decodeUtf8) = .ok values := by
  cases read : readBinary limits node nullable input with
  | error cause => simp [readUtf8, ← readBinary_iff, read, bind, Except.bind]
  | ok slots => simp [readUtf8, ← readBinary_iff, read, bind, Except.bind]

private theorem decodeUtf8Slot_null {slot : Option KBytes} {value : Option String}
    (read : slot.mapM decodeUtf8 = .ok value) : value.isNone = slot.isNone := by
  cases slot with
  | none =>
    have same : none = value := by simpa [pure, Except.pure] using read
    simp [← same]
  | some bytes =>
    cases decoded : decodeUtf8 bytes with
    | error cause => simp [decoded, Functor.map, Except.map] at read
    | ok text =>
      have same : some text = value := by simpa [decoded, Functor.map, Except.map] using read
      simp [← same]

private theorem decodeUtf8Slots_counts {slots : List (Option KBytes)} {values : List (Option String)}
    (read : slots.mapM (·.mapM decodeUtf8) = .ok values) :
    values.length = slots.length ∧ values.countP Option.isNone = slots.countP Option.isNone := by
  induction slots generalizing values with
  | nil =>
    have same : [] = values := by simpa [pure, Except.pure] using read
    simp [← same]
  | cons slot rest ih =>
    cases first : slot.mapM decodeUtf8 with
    | error cause => simp [List.mapM_cons, first, bind, Except.bind] at read
    | ok value =>
      cases tail : rest.mapM (·.mapM decodeUtf8) with
      | error cause => simp [List.mapM_cons, first, tail, bind, Except.bind] at read
      | ok values' =>
        simp [List.mapM_cons, first, tail, bind, Except.bind, pure, Except.pure] at read
        subst values
        obtain ⟨length, nulls⟩ := ih tail
        simp [length, nulls, decodeUtf8Slot_null first, List.countP_cons]

theorem readUtf8_counts {limits : Limits} {node : FieldNode} {nullable : Bool} {input : Buffers}
    {values : List (Option String)} (read : readUtf8 limits node nullable input = .ok values) :
    values.length = node.length ∧ values.countP Option.isNone = node.nullCount := by
  obtain ⟨slots, wire, decoded⟩ := (readUtf8_iff _ _ _ _ _).1 read
  obtain ⟨length, nulls⟩ := decodeUtf8Slots_counts decoded
  exact ⟨length.trans ((slots_length wire.2.1).trans List.length_range), nulls.trans wire.2.2.1⟩

end Silmaril.Proofs.Formats.Arrow.BinaryView.Column
