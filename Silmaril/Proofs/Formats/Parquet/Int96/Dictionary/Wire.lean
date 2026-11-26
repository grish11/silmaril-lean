module

public import Silmaril.Formats.Parquet.Int96.Dictionary.Defs
public import Batteries.Data.List.Basic
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.Int96.Page.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Footer.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.Int96.Dictionary

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int96 Silmaril.Formats.Parquet.Int96.Dictionary

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

private theorem cons_ok {α ε : Type} {head : Except ε α} {tail : Except ε (List α)} {out : List α}
    (h : (do let a ← head; let as ← tail; pure (a :: as)) = .ok out) :
    ∃ a as, head = .ok a ∧ tail = .ok as ∧ out = a :: as := by
  obtain ⟨a, first, h⟩ := bind_ok h
  obtain ⟨as, rest, h⟩ := bind_ok h
  exact ⟨a, as, first, rest, (Except.ok.inj h).symm⟩

private theorem mapM_order {α β ε : Type} (read : α → Except ε β)
    {inputs : List α} {outputs : List β} (h : inputs.mapM read = .ok outputs) :
    List.Forall₂ (fun input output => read input = .ok output) inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases h; exact .nil
  | cons first rest ih =>
    rw [List.mapM_cons] at h
    obtain ⟨a, as, head, tail, rfl⟩ := cons_ok h
    exact .cons head (ih tail)

private theorem selectSlots_cons {α : Type} (dictionary : Array α) (start : Nat)
    (reference : Option Nat) (rest : List (Option Nat)) :
    selectSlots dictionary start (reference :: rest) = (do
      let value ← selectSlot dictionary start reference
      let values ← selectSlots dictionary (start + 1) rest
      pure (value :: values)) := by
  simp only [selectSlots, List.zipIdx_cons, List.mapM_cons]

theorem selectSlots_ordered {α : Type} {dictionary : Array α} {start : Nat}
    {references : List (Option Nat)} {slots : List (Option α)}
    (h : selectSlots dictionary start references = .ok slots) :
    List.Forall₂ (SlotMatches dictionary) references slots := by
  induction references generalizing start slots with
  | nil => cases h; exact .nil
  | cons reference rest ih =>
    rw [selectSlots_cons] at h
    obtain ⟨value, values, first, tail, rfl⟩ := cons_ok h
    refine .cons ?_ (ih tail)
    cases reference with
    | none => simpa [selectSlot, SlotMatches, eq_comm] using first
    | some index =>
      cases lookup : dictionary[index]? with
      | none => simp [selectSlot, lookup] at first
      | some entry =>
        have valueEq : some entry = value := by simpa [selectSlot, lookup] using first
        exact ⟨entry, lookup, valueEq.symm⟩

theorem selectSlots_reference_error {α : Type} {dictionary : Array α} {start : Nat}
    {references : List (Option Nat)} {slot index : Nat}
    (h : selectSlots dictionary start references = .error (.reference slot index)) :
    ∃ before after, references = before ++ some index :: after ∧ slot = start + before.length ∧
      dictionary[index]? = none ∧ ∃ prefixSlots, selectSlots dictionary start before = .ok prefixSlots := by
  induction references generalizing start with
  | nil => simp [selectSlots, Pure.pure, Except.pure] at h
  | cons reference rest ih =>
    rw [selectSlots_cons] at h
    cases first : selectSlot dictionary start reference with
    | error cause =>
      have same : cause = .reference slot index := by
        simpa [first, Bind.bind, Except.bind] using h
      subst cause
      cases reference with
      | none => simp [selectSlot] at first
      | some actual =>
        cases lookup : dictionary[actual]? with
        | some entry => simp [selectSlot, lookup] at first
        | none =>
          have same : start = slot ∧ actual = index := by simpa [selectSlot, lookup] using first
          obtain ⟨rfl, rfl⟩ := same
          exact ⟨[], rest, rfl, rfl, lookup, [], rfl⟩
    | ok value =>
      have remaining : selectSlots dictionary (start + 1) rest = .error (.reference slot index) := by
        cases tail : selectSlots dictionary (start + 1) rest <;>
          simp_all [Bind.bind, Except.bind, Pure.pure, Except.pure]
      obtain ⟨before, after, rfl, position, bad, values, prefixOk⟩ := ih remaining
      refine ⟨reference :: before, after, rfl, ?_, bad, value :: values, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm 1] using position
      · simp [selectSlots_cons, first, prefixOk, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem slot_masks {α : Type} {dictionary : Array α}
    {references : List (Option Nat)} {slots : List (Option α)}
    (ordered : List.Forall₂ (SlotMatches dictionary) references slots) :
    slots.map Option.isSome = references.map Option.isSome := by
  induction ordered with
  | nil => rfl
  | @cons reference value _ _ first _ ih =>
    cases reference with
    | none =>
      have same : value = none := first
      simp [same, ih]
    | some index =>
      obtain ⟨_, _, rfl⟩ := first
      simp [ih]

theorem decodeData_wire {limits : Limits} {policy : Policy}
    {dictionary : Array (Int96.Page.Value policy)} {params : ScalarPage.Parameters} {body : Bytes}
    {slots : Slots policy} (h : decodeData limits dictionary params body = .ok slots) :
    ∃ layout prepared references raw, ∃ width : UInt8, ∃ runs : List UInt8,
      ScalarPage.validateFor 8 params limits.scalar body = .ok layout ∧
      ScalarPage.PreparedWire params limits.scalar layout body prepared ∧
      DictionaryIndex.readIndices limits.indices (prepared.mask.count true) prepared.scalars = .ok references ∧
      prepared.scalars.toList = width :: runs ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs references ∧
      raw.map Option.isSome = prepared.mask ∧ raw.filterMap id = references ∧
      List.Forall₂ (SlotMatches dictionary) raw slots ∧ slots.map Option.isSome = prepared.mask ∧
      slots.length = params.numValues := by
  unfold decodeData at h
  obtain ⟨prepared, parsed, h⟩ := bind_ok h
  obtain ⟨references, indexed, h⟩ := bind_ok h
  obtain ⟨raw, reconstructed, selected⟩ := bind_ok h
  have parsed := mapError_ok parsed
  obtain ⟨layout, checked, wire⟩ := ScalarPage.prepareFor_sound parsed
  obtain ⟨mask, ordered⟩ := FlatPage.reconstruct_ok_iff.mp (mapError_ok reconstructed)
  have placed := selectSlots_ordered selected
  have sameMask := (slot_masks placed).trans mask
  have count := (ScalarPage.preparedFor_counts parsed).1
  rw [← sameMask, List.length_map] at count
  have indexed := mapError_ok indexed
  obtain ⟨_, width, runs, bytes, _, _, _, stream⟩ := DictionaryIndex.readIndices_ok_iff.mp indexed
  exact ⟨layout, prepared, references, raw, width, runs, checked, wire, indexed, bytes,
    stream, mask, ordered, placed, sameMask, count⟩

theorem readDictionary_wire {limits : Limits} {policy : Policy} {source : Bytes}
    {frame : Parquet.Page.Frame} {dictionary : Array (Int96.Page.Value policy)}
    (h : readDictionary limits policy source frame = .ok dictionary) :
    ∃ (header : Parquet.Page.Dictionary) (entries : List Int96.Payload),
      frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧ frame.value.crc = none ∧
      frame.value.compressedSize = frame.value.uncompressedSize ∧
      header.numValues ≤ limits.maxEntries ∧ frame.value.compressedSize ≤ limits.maxDictionaryBytes ∧
      entries.length = header.numValues ∧
      (frameBody source frame).toList = entries.flatMap Int96.Payload.encode ∧
      dictionary = (entries.map (·.toTicks policy)).toArray := by
  cases kind : frame.value.kind <;>
    simp only [readDictionary, kind] at h <;> try contradiction
  rename_i header
  split at h <;> try contradiction
  rename_i noChecksum
  split at h <;> try contradiction
  rename_i sameSize
  split at h <;> try contradiction
  rename_i plainEncoding
  split at h <;> try contradiction
  rename_i entryCap
  split at h <;> try contradiction
  rename_i byteCap
  obtain ⟨words, physicalRead, h⟩ := bind_ok h
  obtain ⟨slots, wordRead, result⟩ := bind_ok h
  have physicalRead := mapError_ok physicalRead
  have fixed : Plain.decodeFixedWidth 12 header.numValues Bytes.ofList (frameBody source frame) =
      .ok words := by
    simpa only [Plain.decodeFixedLenBytes, ite_eq_left (by decide : 12 < (2 : Nat) ^ 31)] using physicalRead
  obtain ⟨_, chunks, exactBody, length, _, ordered⟩ := Plain.decodeFixedWidth_ok_iff.mp fixed
  have returned := (Int96.Page.decodeSlots_eq_ok_iff _ _ _).mp (mapError_ok wordRead)
  have exactWords : chunks = (slots.filterMap id).map Int96.Payload.encode := by
    rw [ordered] at returned
    simpa [List.map_map, List.filterMap_map, List.map_filterMap, Function.comp_def] using
      congrArg (List.filterMap id) returned
  have noCRC : frame.value.crc = none := by
    cases crc : frame.value.crc <;> simp_all
  refine ⟨header, slots.filterMap id, rfl, not_ne_iff.mp plainEncoding, noCRC,
    not_ne_iff.mp sameSize, Nat.le_of_not_gt entryCap, Nat.le_of_not_gt byteCap, ?_, ?_,
    (Except.ok.inj result).symm⟩
  · simpa [exactWords] using length
  · rw [exactBody, exactWords, List.flatMap_def]

theorem decodeData_reference_error {limits : Limits} {policy : Policy}
    {dictionary : Array (Int96.Page.Value policy)} {params : ScalarPage.Parameters}
    {body : Bytes} {slot index : Nat}
    (h : decodeData limits dictionary params body = .error (.reference slot index)) :
    ∃ prepared references before after,
      ScalarPage.prepareFor 8 params limits.scalar body = .ok prepared ∧
      DictionaryIndex.readIndices limits.indices (prepared.mask.count true) prepared.scalars = .ok references ∧
      FlatPage.reconstruct prepared.mask references = .ok (before ++ some index :: after) ∧
      slot = before.length ∧ dictionary[index]? = none ∧
      ∃ prefixSlots, selectSlots dictionary 0 before = .ok prefixSlots := by
  cases parsed : ScalarPage.prepareFor 8 params limits.scalar body with
  | error error => simp [decodeData, parsed, Bind.bind, Except.bind, Except.mapError] at h
  | ok prepared =>
    cases indexed : DictionaryIndex.readIndices limits.indices (prepared.mask.count true) prepared.scalars with
    | error error => simp [decodeData, parsed, indexed, Bind.bind, Except.bind, Except.mapError] at h
    | ok references =>
      cases reconstructed : FlatPage.reconstruct prepared.mask references with
      | error error => simp [decodeData, parsed, indexed, reconstructed, Bind.bind, Except.bind, Except.mapError] at h
      | ok raw =>
        have selected : selectSlots dictionary 0 raw = .error (.reference slot index) := by
          simpa [decodeData, parsed, indexed, reconstructed, Bind.bind, Except.bind, Except.mapError] using h
        obtain ⟨before, after, rfl, position, bad, prefixSlots, prefixOk⟩ :=
          selectSlots_reference_error selected
        exact ⟨prepared, references, before, after, rfl, indexed, reconstructed,
          by simpa using position, bad, prefixSlots, prefixOk⟩

theorem locate_span {limits : Limits} {footerStart rowCount : Nat} {leaf : Footer.SchemaElement}
    {column : Footer.ColumnMetadata} {span : Footer.Span}
    (h : locate limits footerStart rowCount leaf column = .ok span) :
    Parquet.Page.columnSpan footerStart column = some span ∧
      column.dictionaryPageOffset = some (span.start : Int) := by
  unfold locate at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hasDictionary
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i actual selected
  cases h
  refine ⟨selected, ?_⟩
  cases offset : column.dictionaryPageOffset with
  | none => simp [offset] at hasDictionary
  | some offsetValue =>
    have exactSpan : Footer.checkDataSpan footerStart offsetValue column.totalCompressedSize =
        some span := by
      simpa [Parquet.Page.columnSpan, offset] using selected
    rw [(Footer.checkDataSpan_some_iff.mp exactSpan).1]

private theorem pages_ordered {limits : Limits} {source : Bytes} {leaf : Footer.SchemaElement}
    {policy : Policy} {dictionary : Array (Int96.Page.Value policy)}
    {frames : List (Parquet.Page.Frame × Nat)}
    {planned : List (Parquet.Page.Frame × Nat × ScalarPage.Parameters)}
    {pages : List (Slots policy)}
    (plan : List.Forall₂ (fun entry item =>
      ((dataParameters leaf entry.1.value).map (fun params => (entry.1, entry.2, params))).mapError
        (atPage entry.2 entry.1) = .ok item) frames planned)
    (decoded : List.Forall₂ (fun (frame, ordinal, params) slots =>
      (decodeData limits dictionary params (frameBody source frame)).mapError
        (atPage ordinal frame) = .ok slots) planned pages) :
    List.Forall₂ (fun frame slots => ∃ params, dataParameters leaf frame.value = .ok params ∧
      decodeData limits dictionary params (frameBody source frame) = .ok slots)
      (frames.map Prod.fst) pages ∧
      (pages.map List.length).sum = (planned.map (fun (_, _, params) => params.numValues)).sum := by
  induction plan generalizing pages with
  | nil =>
    cases decoded
    exact ⟨.nil, rfl⟩
  | @cons entry item rest following chosen plannedTail ih =>
    cases decoded with
    | cons first tail =>
      have chosen := mapError_ok chosen
      cases checkedParams : dataParameters leaf entry.1.value with
      | error error => simp [checkedParams, Except.map] at chosen
      | ok params =>
        simp [checkedParams, Except.map] at chosen
        subst item
        have read := mapError_ok first
        obtain ⟨ordered, count⟩ := ih tail
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, pageCount⟩ := decodeData_wire read
        exact ⟨.cons ⟨params, checkedParams, read⟩ ordered, by simp [pageCount, count]⟩

theorem read_framed_wire {limits : Limits} {policy : Policy} {source : Bytes} {footerStart rowCount : Nat}
    {leaf : Footer.SchemaElement} {column : Footer.ColumnMetadata} {slots : Slots policy}
    (h : Dictionary.read limits policy source footerStart rowCount leaf column = .ok slots) :
    ∃ span first rest dictionary pages,
      Parquet.Page.columnSpan footerStart column = some span ∧
      Parquet.Page.readChunk limits.framing source span = .ok (first :: rest) ∧
      Parquet.Page.Chain span span.start span.stop (first :: rest) ∧
      column.dictionaryPageOffset = some (first.header.start : Int) ∧
      rest.head?.map (fun frame => (frame.header.start : Int)) = some column.dataPageOffset ∧
      readDictionary limits policy source first = .ok dictionary ∧
      List.Forall₂ (fun frame page => ∃ params, dataParameters leaf frame.value = .ok params ∧
        decodeData limits dictionary params (frameBody source frame) = .ok page) rest pages ∧
      slots = pages.flatten ∧ slots.length = rowCount := by
  unfold Dictionary.read at h
  have h := mapError_ok h
  unfold Dictionary.read.readChunk at h
  obtain ⟨span, located, h⟩ := bind_ok h
  obtain ⟨frames, framed, h⟩ := bind_ok h
  have framed := mapError_ok framed
  cases frames with
  | nil => contradiction
  | cons first rest =>
    obtain ⟨dictionary, readDictionaryOk, h⟩ := bind_ok h
    obtain ⟨_, offsetOk, h⟩ := bind_ok h
    obtain ⟨planned, plannedOk, h⟩ := bind_ok h
    obtain ⟨_, rowsOk, h⟩ := bind_ok h
    obtain ⟨pages, decoded, h⟩ := bind_ok h
    have result : pages.flatten = slots := Except.ok.inj h
    have ⟨ordered, count⟩ := pages_ordered (mapM_order _ plannedOk) (mapM_order _ decoded)
    have ⟨spanOk, dictionaryOffset⟩ := locate_span located
    have chain := (Parquet.Page.readChunk_chain framed).2.2
    have firstAt {start stop : Nat} (framed : Parquet.Page.Chain span start stop (first :: rest)) :
        first.header.start = start := by
      cases framed with
      | cons within _ => exact within.headerStart
    have headerStart := firstAt chain
    have dataOffset : rest.head?.map (fun frame => (frame.header.start : Int)) = some column.dataPageOffset := by
      cases rest with
      | nil => simp [checkDataOffset] at offsetOk
      | cons firstData remaining =>
        by_cases equal : (firstData.header.start : Int) = column.dataPageOffset
        · simp [equal]
        · simp [checkDataOffset, equal] at offsetOk
    refine ⟨span, first, rest, dictionary, pages, spanOk, framed, chain, ?_, dataOffset,
      mapError_ok readDictionaryOk, ?_, result.symm, ?_⟩
    · rwa [headerStart]
    · simpa using ordered
    · rw [← result, List.length_flatten, count]
      simpa [checkSlotCount] using rowsOk

theorem read_wire {limits : Limits} {policy : Policy} {source : Bytes} {footerStart rowCount : Nat}
    {leaf : Footer.SchemaElement} {column : Footer.ColumnMetadata} {slots : Slots policy}
    (h : Dictionary.read limits policy source footerStart rowCount leaf column = .ok slots) :
    ∃ span first rest dictionary pages,
      Parquet.Page.columnSpan footerStart column = some span ∧
      Parquet.Page.Chain span span.start span.stop (first :: rest) ∧
      column.dictionaryPageOffset = some (first.header.start : Int) ∧
      rest.head?.map (fun frame => (frame.header.start : Int)) = some column.dataPageOffset ∧
      readDictionary limits policy source first = .ok dictionary ∧
      List.Forall₂ (fun frame page => ∃ params, dataParameters leaf frame.value = .ok params ∧
        decodeData limits dictionary params (frameBody source frame) = .ok page) rest pages ∧
      slots = pages.flatten ∧ slots.length = rowCount := by
  obtain ⟨span, first, rest, dictionary, pages, spanOk, _, chain, dictionaryOffset,
    dataOffset, dictionaryOk, ordered, flattened, count⟩ := read_framed_wire h
  exact ⟨span, first, rest, dictionary, pages, spanOk, chain, dictionaryOffset,
    dataOffset, dictionaryOk, ordered, flattened, count⟩

theorem readDictionary_entry_error {limits : Limits} {policy : Policy} {source : Bytes}
    {frame : Parquet.Page.Frame} {index : Nat}
    (h : readDictionary limits policy source frame = .error (.dictionaryEntry (.invalidWord index))) :
    ∃ header words before bad after,
      frame.value.kind = .dictionary header ∧
      Plain.decodeFixedLenBytes 12 header.numValues (frameBody source frame) = .ok words ∧
      words.map some = before ++ some bad :: after ∧
      (∃ entries, Int96.Page.decodeSlots 0 before = .ok entries) ∧
      Payload.decode? bad.toList = none ∧ index = before.length := by
  cases kind : frame.value.kind <;>
    simp only [readDictionary, kind] at h <;> simp at h
  rename_i header
  split at h <;> try (simp at h)
  split at h <;> try (simp at h)
  split at h <;> try (simp at h)
  split at h <;> try (simp at h)
  split at h <;> try (simp at h)
  cases physical : Plain.decodeFixedLenBytes 12 header.numValues (frameBody source frame) with
  | error cause => simp [physical, Bind.bind, Except.bind, Except.mapError] at h
  | ok words =>
    have failed : Int96.Page.decodeSlots 0 (words.map some) = .error (.invalidWord index) := by
      cases interpreted : Int96.Page.decodeSlots 0 (words.map some) <;>
        simp_all [Bind.bind, Except.bind, Except.mapError]
    obtain ⟨before, bad, after, ordered, prefixOk, invalid, position⟩ :=
      (Int96.Page.decodeSlots_eq_invalidWord_iff _ _ _).mp failed
    exact ⟨header, words, before, bad, after, rfl, physical, ordered, prefixOk, invalid,
      by simpa using position⟩

end Silmaril.Proofs.Formats.Parquet.Int96.Dictionary
