module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Defs
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ByteArrayFallback

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ByteArrayFallback

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

private theorem mapM_order {α β ε : Type} (read : α → Except ε β)
    {inputs : List α} {outputs : List β} (h : inputs.mapM read = .ok outputs) :
    List.Forall₂ (fun input output => read input = .ok output) inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases h; exact .nil
  | cons first rest ih =>
    rw [List.mapM_cons] at h
    obtain ⟨value, readFirst, h⟩ := bind_ok h
    obtain ⟨values, readRest, h⟩ := bind_ok h
    cases h
    exact .cons readFirst (ih readRest)

private theorem locate_wire {limits : Limits} {leaf : Footer.SchemaElement} {group : Footer.RowGroup}
    {metadata : Footer.ColumnMetadata} {footerStart : Nat} {span : Footer.Span}
    (h : locate limits leaf group metadata footerStart = .ok span) :
    (metadata.pathInSchema = [leaf.name] ∧ metadata.physicalType = .byteArray ∧ metadata.numValues = group.numRows) ∧
    metadata.codec = 0 ∧ Page.columnSpan footerStart metadata = some span := by
  unfold locate at h
  split at h
  · contradiction
  · rename_i matched
    split at h
    · contradiction
    · rename_i codec
      split at h <;> try contradiction
      split at h <;> try contradiction
      split at h <;> try contradiction
      split at h
      · contradiction
      · rename_i selected
        cases h
        exact ⟨Decidable.not_not.mp matched, Decidable.not_not.mp codec, selected⟩

private theorem bodyLimits_ok {maxBytes : Nat} {header : Page.Header}
    (h : bodyLimits maxBytes header = .ok ()) :
    header.crc = none ∧ header.compressedSize ≤ maxBytes ∧ header.compressedSize = header.uncompressedSize := by
  unfold bodyLimits at h
  split at h
  · contradiction
  · rename_i crc
    split at h
    · contradiction
    · rename_i sizes
      split at h
      · contradiction
      · rename_i equal
        exact ⟨Decidable.not_not.mp crc,
          Nat.le_of_not_gt (fun over => sizes (.inl over)), Decidable.not_not.mp equal⟩

theorem readDictionary_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {frame : Page.Frame} {entries : Array Bytes}
    (h : readDictionary limits metadata source frame = .ok entries) : DictionaryWire limits source frame entries := by
  unfold readDictionary at h
  split at h <;> try contradiction
  rename_i header kind
  obtain ⟨accepted, checked, h⟩ := bind_ok h
  cases accepted
  obtain ⟨crc, size, equal⟩ := bodyLimits_ok checked
  split at h <;> try contradiction
  rename_i encoding
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i count
  obtain ⟨values, decoded, h⟩ := bind_ok h
  have decoded := mapError_ok decoded
  obtain ⟨_, wire, length, _⟩ := Plain.ByteArray.decode_ok_iff.mp decoded
  cases h
  exact ⟨header, values, kind, Decidable.not_not.mp encoding, crc, equal, Nat.le_of_not_gt count,
    size, decoded, length, wire, rfl⟩

theorem decodeData_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {dictionary : Option (Array Bytes)} {frame : Page.Frame} {slots : List (Option Bytes)}
    (h : decodeData limits metadata source dictionary frame = .ok slots) : PageWire limits source dictionary frame slots := by
  unfold decodeData at h
  obtain ⟨_, _, h⟩ := bind_ok h
  split at h <;> try contradiction
  rename_i params original
  dsimp only at h
  split at h <;> try contradiction
  rename_i supported
  split at h <;> try contradiction
  split at h <;> try contradiction
  have declared : declaredSlots frame = params.numValues := by simp [declaredSlots, original]
  split at h
  · rename_i plain
    have decoded := mapError_ok h
    obtain ⟨page, values, prepared, scalars, mask, present, _, _⟩ := ScalarPage.decode_sound decoded
    have ⟨layout, valid, exactBody⟩ := ScalarPage.prepare_sound prepared
    obtain ⟨_, wire, _, _⟩ := Plain.ByteArray.decode_ok_iff.mp scalars
    have count := (ScalarPage.decode_counts decoded).1
    exact ⟨params, layout, page, original, by simpa [plain, ScalarPage.validate] using valid,
      exactBody, mask, count.trans declared.symm, .inl ⟨plain, wire.trans (congrArg Plain.ByteArray.wire present.symm)⟩⟩
  · rename_i notPlain
    have indexed : params.encoding = 8 := Decidable.not_not.mp (fun other => supported ⟨notPlain, other⟩)
    cases dictionary with
    | none => contradiction
    | some entries =>
      have decoded := mapError_ok h
      obtain ⟨_, page, indices, prepared, indicesRead, mask, lookup⟩ := DictionaryIndex.decode_ok_iff.mp decoded
      have ⟨layout, valid, exactBody⟩ := ScalarPage.prepareFor_sound prepared
      have count := (DictionaryIndex.decode_counts decoded).1
      exact ⟨params, layout, page, original, valid, exactBody, mask, count.trans declared.symm,
        .inr ⟨indexed, entries, indices, rfl, indicesRead, lookup⟩⟩

private theorem splitLeading_order (frames : List Page.Frame) :
    frames = (splitLeading frames).1.toList ++ (splitLeading frames).2 := by
  cases frames with
  | nil => rfl
  | cons frame rest => cases kind : frame.value.kind <;> simp [splitLeading, kind]

private theorem leading_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {dictionary : Option Page.Frame} {entries : Option (Array Bytes)}
    {fail : Page.Frame → FlatColumn.PageError DecodeError → Error}
    (h : dictionary.mapM (fun frame => (readDictionary limits metadata source frame).mapError (fail frame)) =
      .ok entries) : LeadingWire limits source dictionary entries := by
  cases dictionary with
  | none =>
    cases h
    exact trivial
  | some frame =>
    obtain ⟨values, decoded, h⟩ := bind_ok h
    cases h
    exact readDictionary_wire (mapError_ok decoded)

private theorem pages_count {limits : Limits} {source : Bytes} {entries : Option (Array Bytes)}
    {data : List Page.Frame} {pages : List (List (Option Bytes))}
    (decoded : List.Forall₂ (PageWire limits source entries) data pages) :
    pages.flatten.length = (data.map declaredSlots).sum := by
  induction decoded with
  | nil => rfl
  | cons first _ ih =>
    obtain ⟨_, _, _, _, _, _, _, count, _⟩ := first
    simp [count, ih]

private theorem readFrames_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (h : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits source metadata rows frames slots := by
  unfold readFrames at h
  cases split : splitLeading frames with
  | mk dictionary data =>
    rw [split] at h
    dsimp only at h
    split at h <;> try contradiction
    rename_i offsets
    split at h <;> try contradiction
    rename_i counted
    obtain ⟨entries, opened, h⟩ := bind_ok h
    obtain ⟨pages, decoded, h⟩ := bind_ok h
    have ordered : List.Forall₂ (PageWire limits source entries) data pages := by
      rw [← List.zipIdx_map_fst (if dictionary.isSome then 1 else 0) data, List.forall₂_map_left_iff]
      exact (mapM_order _ decoded).imp (fun _ _ read => decodeData_wire (mapError_ok read))
    have order := splitLeading_order frames
    rw [split] at order
    cases h
    exact ⟨dictionary, data, entries, pages, order, Decidable.not_not.mp (fun e => offsets (.inl e)),
      Decidable.not_not.mp (fun e => offsets (.inr e)),
      leading_wire opened, ordered, rfl, (pages_count ordered).trans (Decidable.not_not.mp counted)⟩

theorem readGroup_wire {name : String} {checked : Checked name} {limits : Limits}
    {index : Nat} {slots : List (Option Bytes)} (h : readGroup checked limits index = .ok slots) :
    GroupWire checked limits index slots := by
  unfold readGroup at h
  split at h <;> try contradiction
  rename_i group selected
  dsimp only at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i column matched
  obtain ⟨span, located, h⟩ := bind_ok h
  obtain ⟨frames, framed, decoded⟩ := bind_ok h
  obtain ⟨⟨path, physical, count⟩, codec, bounded⟩ := locate_wire (mapError_ok located)
  exact ⟨group, column, span, frames, checked.binding.leafAt, selected, matched, path,
    physical, count, codec, bounded, mapError_ok framed, readFrames_wire decoded⟩

end Silmaril.Proofs.Formats.Parquet.ByteArrayFallback
