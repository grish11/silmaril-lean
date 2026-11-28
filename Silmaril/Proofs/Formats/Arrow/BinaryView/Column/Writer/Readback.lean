module

public import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Defs
import Silmaril.Formats.Arrow.BinaryView.Column.Thms
import Silmaril.Formats.Arrow.BinaryView.Thms
import Silmaril.Prelude.Bytes.Thms
import Silmaril.Proofs.Formats.Arrow.BinaryView.Column.Writer
import Init.Data.List.Monadic
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.BinaryView.Column.Writer

open Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.BinaryView.Column
open Silmaril.Formats.Arrow.BinaryView.Column.Writer

private def measure (slot : Option KBytes) : Option (Nat × List UInt8) :=
  slot.map fun bytes => (bytes.len, bytes.toList)

private theorem read_slot {limits : BinaryView.Column.Limits} {nullable : Bool}
    {values : List (Option KBytes)} {result : Emitted} (layout : Layout limits nullable values result)
    (index : Nat) (bound : index < values.length) :
    ∃ value, readSlot result.buffers index limits.valueBytes = .ok value ∧
      measure value = measure values[index] := by
  have physical := layout.slot index bound
  let view := result.buffers.payload.views
  let start := 16 * index
  have full : start + 16 ≤ view.len := by
    change start + 16 ≤ result.buffers.payload.views.len
    rw [layout.viewsSize]
    dsimp [start]
    omega
  have viewWf : view.wf = true := layout.fits.2.2.2.1.2.1
  cases value : values[index] with
  | none =>
    obtain ⟨valid, _⟩ := physical
    rw [value] at valid
    exact ⟨none, by simp [readSlot, valid], rfl⟩
  | some source =>
    simp only [value, SlotEncoding, Option.getD_some, Option.isSome_some] at physical
    obtain ⟨valid, lengthRead, lengthSigned, tail⟩ := physical
    have valueLimit := layout.valueBound _ (List.getElem_mem bound)
    rw [value] at valueLimit
    have valueCap : source.len ≤ limits.valueBytes := valueLimit
    change view.read start 4 = source.len at lengthRead
    by_cases short : source.len ≤ 12
    · rw [ite_eq_left short] at tail
      obtain ⟨zero, octets⟩ := tail
      let chosen := view.slice (start + 4) source.len
      have wire : BinaryView.Wire result.buffers.payload index limits.valueBytes chosen := by
        simp only [BinaryView.Wire]
        rw [lengthRead]
        exact ⟨viewWf, full, lengthSigned, valueCap, .inl ⟨short, zero, rfl⟩⟩
      have decoded := (BinaryView.readBinary_iff _ _ _ _).2 wire
      refine ⟨some chosen, by simp [readSlot, valid, decoded, Except.map, Except.mapError], ?_⟩
      exact congrArg some (Prod.ext (KBytes.len_slice _ _ _) octets)
    · rw [ite_eq_right short] at tail
      obtain ⟨buffer, offsetWord, sign, data, found, dataWf, dataFits, prefixBytes, octets⟩ := tail
      let offset := longBytes KBytes.len (values.take index)
      let chosen := data.slice offset source.len
      have wire : BinaryView.Wire result.buffers.payload index limits.valueBytes chosen := by
        simp only [BinaryView.Wire]
        rw [lengthRead, buffer, offsetWord]
        exact ⟨viewWf, full, lengthSigned, valueCap,
          .inr ⟨by omega, ⟨by decide, sign⟩, data, found, dataWf, dataFits, prefixBytes, rfl⟩⟩
      have decoded := (BinaryView.readBinary_iff _ _ _ _).2 wire
      refine ⟨some chosen, by simp [readSlot, valid, decoded, Except.map, Except.mapError], ?_⟩
      exact congrArg some (Prod.ext (KBytes.len_slice _ _ _) octets)

private theorem traversal {α β γ ε : Type} (inputs : List α)
    (read : α → Except ε β) (actual : β → γ) (expected : α → γ)
    (one : ∀ input ∈ inputs, ∃ value, read input = .ok value ∧ actual value = expected input) :
    ∃ values, inputs.mapM read = .ok values ∧ values.map actual = inputs.map expected := by
  induction inputs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons input rest ih =>
    obtain ⟨value, decoded, observed⟩ := one input (by simp)
    obtain ⟨values, decodedRest, observedRest⟩ := ih (fun v h => one v (List.mem_cons_of_mem _ h))
    exact ⟨value :: values, by simp [List.mapM_cons, decoded, decodedRest, bind, Except.bind, pure, Except.pure],
      by simp [observed, observedRest]⟩

private theorem range_observation (values : List (Option KBytes)) :
    (List.range values.length).map (fun index => measure (values[index]?.getD none)) = values.map measure := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    simp only [List.length_map, List.length_range] at hi
    simp [List.getElem?_eq_getElem hi]

private theorem measure_none (value : Option KBytes) : (measure value).isNone = value.isNone := by
  cases value <;> rfl

private theorem measure_length (value : Option KBytes) :
    ((measure value).map Prod.fst).getD 0 = (value.map KBytes.len).getD 0 := by
  cases value <;> rfl

private theorem read_measured {limits : BinaryView.Column.Limits} {nullable : Bool}
    {values : List (Option KBytes)} {result : Emitted} (layout : Layout limits nullable values result) :
    ∃ decoded, BinaryView.Column.readBinary limits result.node nullable result.buffers = .ok decoded ∧
      decoded.map measure = values.map measure := by
  let expected := fun (index : Nat) => measure (values[index]?.getD none)
  obtain ⟨decoded, checked, observed⟩ := traversal (List.range values.length)
    (fun i => readSlot result.buffers i limits.valueBytes) measure expected (by
      intro index member
      have bound := List.mem_range.mp member
      simpa only [expected, List.getElem?_eq_getElem bound, Option.getD_some]
        using read_slot layout index bound)
  have seen : decoded.map measure = values.map measure := observed.trans (range_observation values)
  have nulls : decoded.countP Option.isNone = values.countP Option.isNone := by
    simpa only [List.countP_map, Function.comp_def, measure_none] using
      congrArg (List.countP Option.isNone) seen
  have bytes : valueByteCount decoded = valueByteCount values := by
    simpa only [valueByteCount, List.map_map, Function.comp_def, measure_length] using
      congrArg (fun (slots : List (Option (Nat × List UInt8))) =>
        (slots.map fun slot => (slot.map Prod.fst).getD 0).sum) seen
  have fit := (BinaryView.Column.checkBuffers_iff _ _ _ _).2 layout.fits
  refine ⟨decoded, ?_, seen⟩
  unfold BinaryView.Column.readBinary
  rw [fit]
  simp only [bind, Except.bind, layout.node]
  simp [checked, nulls, bytes, layout.outputBound]

private theorem onlyOctets (value : Option KBytes) :
    (measure value).map Prod.snd = value.map KBytes.toList := by
  cases value <;> rfl

theorem emitBinary_roundtrip {limits : BinaryView.Column.Limits} {nullable : Bool}
    {values : List (Option KBytes)} {result : Emitted} (written : emitBinary limits nullable values = .ok result) :
    ∃ decoded, BinaryView.Column.readBinary limits result.node nullable result.buffers = .ok decoded ∧
      decoded.map (·.map KBytes.toList) = values.map (·.map KBytes.toList) := by
  obtain ⟨decoded, read, seen⟩ := read_measured (emitBinary_layout written)
  refine ⟨decoded, read, ?_⟩
  simpa only [List.map_map, Function.comp_def, onlyOctets] using
    congrArg (List.map (fun x : Option (Nat × List UInt8) => x.map Prod.snd)) seen

private theorem decode_utf8 {value : Option KBytes} {text : Option String}
    (same : measure value = measure (text.map utf8Bytes)) :
    value.mapM decodeUtf8 = .ok text := by
  cases value with
  | none => cases text <;> simp_all [measure, Option.mapM, pure, Except.pure]
  | some value =>
    cases text with
    | none => simp [measure] at same
    | some text =>
      have bytes : value.toByteArray = text.toByteArray := by
        apply ByteArray.ext
        apply Array.toList_inj.mp
        change value.toList = text.toByteArray.data.toList
        simpa [measure, utf8Octets] using (Option.some.inj same |> congrArg Prod.snd)
      simp [Option.mapM, decodeUtf8, bytes, String.fromUTF8?, text.isValidUTF8,
        Functor.map, Except.map]

private theorem decode_slots {decoded : List (Option KBytes)} {values : List (Option String)}
    (same : decoded.map measure = (values.map (·.map utf8Bytes)).map measure) :
    decoded.mapM (·.mapM decodeUtf8) = .ok values := by
  induction values generalizing decoded with
  | nil =>
    cases decoded with
    | nil => rfl
    | cons => simp at same
  | cons value rest ih =>
    cases decoded with
    | nil => simp at same
    | cons first tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      simp [List.mapM_cons, decode_utf8 same.1, ih same.2, bind, Except.bind, pure, Except.pure]

theorem emitUtf8_roundtrip {limits : BinaryView.Column.Limits} {nullable : Bool}
    {values : List (Option String)} {result : Emitted} (written : emitUtf8 limits nullable values = .ok result) :
    BinaryView.Column.readUtf8 limits result.node nullable result.buffers = .ok values := by
  obtain ⟨decoded, read, seen⟩ := read_measured (emitUtf8_layout written)
  simpa only [BinaryView.Column.readUtf8, read, bind, Except.bind] using decode_slots seen

end Silmaril.Proofs.Formats.Arrow.BinaryView.Column.Writer
