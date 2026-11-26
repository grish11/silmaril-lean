module

public import Silmaril.Formats.Parquet.DictionaryChunk.Defs
public import Batteries.Data.List.Basic
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.DictionaryChunk

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.DictionaryChunk

private theorem bind_ok {ε α β : Type} {input : Except ε α} {f : α → Except ε β} {out : β}
    (success : (input >>= f) = .ok out) : ∃ a, input = .ok a ∧ f a = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => exact ⟨a, rfl, success⟩

private theorem mapError_ok {ε δ α : Type} {input : Except ε α} {f : ε → δ} {out : α}
    (success : input.mapError f = .ok out) : input = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => cases success; rfl

private theorem mapM_order {ε α β : Type} (f : α → Except ε β) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys →
      List.Forall₂ (fun x y => f x = .ok y) xs ys
  | [], _, h => by cases h; exact .nil
  | x :: xs, _, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := bind_ok h
    obtain ⟨ys, hys, h⟩ := bind_ok h
    cases h
    exact .cons hy (mapM_order f hys)

private theorem splitLeading_frames (frames : List Page.Frame) :
    (Internal.splitLeading frames).1.toList ++ (Internal.splitLeading frames).2 = frames := by
  cases frames with
  | nil => rfl
  | cons frame rest =>
    cases h : frame.value.kind <;> simp [Internal.splitLeading, h]

private theorem plain_count {count : Nat} {bytes : Bytes} {entries : List Int32}
    (decoded : Plain.decodeInt32 count bytes = .ok entries) : entries.length = count := by
  rw [Plain.decodeInt32, Plain.decodeFixedWidth_ok_iff] at decoded
  obtain ⟨_, words, _, count, _, rfl⟩ := decoded
  simpa using count

private theorem readDictionary_ok {limits : Limits} {source : Bytes} {frame : Page.Frame}
    {dictionary : Dictionary} (parsed : Internal.readDictionary limits source frame = .ok dictionary) :
    dictionary.frame = frame ∧ dictionary.Exact limits source := by
  unfold Internal.readDictionary at parsed
  split at parsed <;> try contradiction
  rename_i header hkind
  split at parsed <;> try contradiction
  rename_i hcrc
  split at parsed <;> try contradiction
  rename_i hencoding
  split at parsed <;> try contradiction
  rename_i hcount
  split at parsed <;> try contradiction
  rename_i hbytes
  split at parsed <;> try contradiction
  rename_i hsize
  obtain ⟨entries, decoded, ret⟩ := bind_ok parsed
  have decoded := mapError_ok decoded
  cases ret
  simp only [ne_eq, Nat.not_lt, not_not, not_and_or] at hcrc hencoding hcount hbytes hsize
  exact ⟨rfl, header, entries, hkind, hencoding, hcrc, hcount, hbytes, hsize, decoded, rfl,
    plain_count decoded⟩

private theorem parameters_data {layout : FlatPage.Layout} {header : Page.Header}
    {params : ScalarPage.Parameters} (admitted : Internal.dataParameters layout header = .ok params) :
    ((∃ info, header.kind = .dataV1 info) ∨ (∃ info, header.kind = .dataV2 info)) ∧
    params.sizes = ⟨header.compressedSize, header.uncompressedSize⟩ ∧
    params.schema = ⟨0, if layout == .required then 0 else 1⟩ := by
  cases h : header.kind with
  | dataV1 info =>
    simp only [Internal.dataParameters, h] at admitted
    by_cases invalid :
        Internal.levelTag (if layout == .required then 0 else 1) info.definitionLevelEncoding ≠ 3 ∨
          Internal.levelTag 0 info.repetitionLevelEncoding ≠ 3
    · rw [ite_eq_left invalid] at admitted
      contradiction
    · rw [ite_eq_right invalid] at admitted
      cases admitted
      exact ⟨.inl ⟨info, rfl⟩, rfl, rfl⟩
  | dataV2 info =>
    simp only [Internal.dataParameters, h] at admitted
    cases admitted
    exact ⟨.inr ⟨info, rfl⟩, rfl, rfl⟩
  | dictionary _ | skipped _ => simp [Internal.dataParameters, h] at admitted

private theorem admitData_ok {limits : Limits} {layout : FlatPage.Layout}
    {dictionary : Option Dictionary} {frame : Page.Frame} {page : DataPage}
    (admitted : Internal.admitData limits layout dictionary frame = .ok page) :
    page.frame = frame ∧ page.Admitted limits layout dictionary := by
  unfold Internal.admitData at admitted
  obtain ⟨params, hparams, admitted⟩ := bind_ok admitted
  split at admitted <;> try contradiction
  rename_i hcrc
  split at admitted <;> try contradiction
  rename_i hbytes
  split at admitted <;> try contradiction
  rename_i hsize
  split at admitted <;> try contradiction
  rename_i hencoding
  split at admitted <;> try contradiction
  rename_i hdictionary
  cases admitted
  simp only [ne_eq, Nat.not_lt, not_not, not_or, not_and_or] at hcrc hbytes hencoding hdictionary
  obtain ⟨kind, sizes, schema⟩ := parameters_data hparams
  refine ⟨rfl, kind, sizes, schema, hcrc, hbytes.1, hbytes.2, ?_⟩
  rcases hdictionary with plain | present
  · exact .inl plain
  · rcases hencoding with plain | encoding
    · exact .inl plain
    · exact .inr ⟨encoding, by cases dictionary <;> simp_all⟩

private theorem data_order {limits : Limits} {layout : FlatPage.Layout} {dictionary : Option Dictionary}
    {frames : List Page.Frame} {data : List DataPage}
    (admitted : frames.mapM (Internal.admitData limits layout dictionary) = .ok data) :
    data.map (·.frame) = frames ∧ ∀ page ∈ data, page.Admitted limits layout dictionary := by
  have ordered := mapM_order _ admitted
  clear admitted
  induction ordered with
  | nil => simp
  | cons hp _ ih =>
    obtain ⟨rfl, h⟩ := admitData_ok hp
    refine ⟨by simp [ih.1], ?_⟩
    intro page member
    rcases List.mem_cons.mp member with rfl | tail
    · exact h
    · exact ih.2 page tail

private theorem dictionary_order {limits : Limits} {source : Bytes} {leading : Option Page.Frame}
    {dictionary : Option Dictionary}
    (admitted : leading.mapM (Internal.readDictionary limits source) = .ok dictionary) :
    dictionary.map (·.frame) = leading ∧ ∀ d, dictionary = some d → d.Exact limits source := by
  cases leading with
  | none => cases admitted; simp
  | some frame =>
    change (Internal.readDictionary limits source frame >>= fun d => pure (some d)) = _ at admitted
    obtain ⟨d, hd, ret⟩ := bind_ok admitted
    cases ret
    obtain ⟨rfl, valid⟩ := readDictionary_ok hd
    simpa using valid

private theorem admit_ok {limits : Limits} {source : Bytes} {span : Footer.Span} {layout : FlatPage.Layout}
    {rowCount : Nat} {column : Footer.ColumnMetadata} {frames : List Page.Frame} {chunk : Chunk}
    (admitted : Internal.admit limits source span layout rowCount column frames = .ok chunk) :
    chunk.span = span ∧ chunk.frames = frames ∧
    chunk.dictionary.map (fun d => (d.frame.header.start : Int)) = column.dictionaryPageOffset ∧
    chunk.data.head?.map (fun p => (p.frame.header.start : Int)) = some column.dataPageOffset ∧
    (∀ d, chunk.dictionary = some d → d.Exact limits source) ∧
    (∀ page ∈ chunk.data, page.Admitted limits layout chunk.dictionary) ∧
    (chunk.data.map (·.params.numValues)).sum = rowCount := by
  unfold Internal.admit at admitted
  dsimp only at admitted
  split at admitted <;> try contradiction
  rename_i hDictionaryOffset
  split at admitted <;> try contradiction
  rename_i hDataOffset
  obtain ⟨dictionary, hdictionary, admitted⟩ := bind_ok admitted
  obtain ⟨data, hdata, admitted⟩ := bind_ok admitted
  split at admitted <;> try contradiction
  rename_i hCount
  cases admitted
  obtain ⟨hd, typed⟩ := dictionary_order hdictionary
  obtain ⟨hp, pages⟩ := data_order hdata
  simp only [ne_eq, not_not] at hDictionaryOffset hDataOffset hCount
  refine ⟨rfl, ?_, ?_, ?_, typed, pages, hCount⟩
  · simpa [Chunk.frames, hp, ← Option.toList_map, hd] using splitLeading_frames frames
  · have atOffset := congrArg (Option.map (fun frame : Page.Frame => (frame.header.start : Int))) hd
    simpa [Option.map_map, Function.comp_def] using atOffset.trans hDictionaryOffset
  · have atOffset := congrArg (Option.map (fun frame : Page.Frame => (frame.header.start : Int)))
      (congrArg List.head? hp)
    simpa [List.head?_map, Option.map_map, Function.comp_def] using atOffset.trans hDataOffset

theorem read_admitted {limits : Limits} {source : Bytes} {footerStart rowCount : Nat}
    {field : FlatScan.Field} {column : Footer.ColumnMetadata} {chunk : Chunk}
    (parsed : DictionaryChunk.read limits source footerStart field rowCount column = .ok chunk) :
    Admitted limits source footerStart rowCount field.layout column chunk := by
  unfold DictionaryChunk.read at parsed
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  rename_i span hspan
  obtain ⟨frames, hframes, parsed⟩ := bind_ok parsed
  obtain ⟨spanEq, ordered, dictionaryOffset, dataOffset, dictionary, data, sum⟩ := admit_ok parsed
  refine ⟨hspan.trans (congrArg some spanEq.symm), ?_, dictionaryOffset, dataOffset, dictionary, data, sum⟩
  · rw [spanEq, ordered]
    exact mapError_ok hframes

theorem read_payloads {limits : Limits} {source : Bytes} {footerStart rowCount : Nat}
    {field : FlatScan.Field} {column : Footer.ColumnMetadata} {chunk : Chunk}
    (parsed : DictionaryChunk.read limits source footerStart field rowCount column = .ok chunk) :
    ∀ frame ∈ chunk.frames, Page.FrameWithin chunk.span frame.header.start frame ∧
      (body source frame).length = frame.value.compressedSize := by
  have frames := (read_admitted parsed).frames
  intro frame member
  have within := Page.readChunk_payloads_bounded frames frame member
  refine ⟨within, ?_⟩
  have sourceStop := (Page.readChunk_chain frames).2.1
  have stop := Nat.le_trans within.chunkStop sourceStop
  change frame.payload.stop ≤ source.data.size at stop
  change (source.data.extract frame.payload.start frame.payload.stop).size = _
  rw [ByteArray.size_extract, Nat.min_eq_left stop, within.payloadWidth, Nat.add_sub_cancel_left]

private theorem decodePage_wire {limits : Limits} {source : Bytes} {dictionary : Option Dictionary}
    {page : DataPage} {slots : List (Option Int32)}
    (decoded : Internal.decodePage limits source dictionary page = .ok slots) :
    page.Decodes limits source dictionary slots := by
  unfold Internal.decodePage at decoded
  split at decoded
  · rename_i plain
    exact .inl ⟨plain, mapError_ok decoded⟩
  · cases h : dictionary with
    | none => simp [h] at decoded
    | some d =>
      rw [h] at decoded
      exact .inr ⟨d, rfl, mapError_ok decoded⟩

theorem scanColumn_ordered {limits : Limits} {source : Bytes} {footerStart rowCount : Nat}
    {field : FlatScan.Field} {column : Footer.ColumnMetadata} {slots : List (Option Int32)}
    (decoded : scanColumn limits source footerStart field rowCount column = .ok slots) :
    ∃ chunk pages,
      DictionaryChunk.read limits source footerStart field rowCount column = .ok chunk ∧
      List.Forall₂ (DataPage.Decodes limits source chunk.dictionary) chunk.data pages ∧
      slots = pages.flatten ∧ slots.length = rowCount ∧ (field.layout = .required → none ∉ slots) := by
  unfold scanColumn at decoded
  obtain ⟨chunk, admitted, decoded⟩ := bind_ok decoded
  obtain ⟨pages, frames, decoded⟩ := bind_ok decoded
  dsimp only at decoded
  split at decoded <;> try contradiction
  rename_i count
  split at decoded <;> try contradiction
  rename_i required
  cases decoded
  have ordered := (mapM_order _ frames).imp (fun _ _ h => decodePage_wire h)
  refine ⟨chunk, pages, admitted, ordered, rfl, not_not.mp count, ?_⟩
  intro layout missing
  exact required ⟨layout, List.any_eq_true.mpr ⟨none, missing, rfl⟩⟩

end Silmaril.Proofs.Formats.Parquet.DictionaryChunk
