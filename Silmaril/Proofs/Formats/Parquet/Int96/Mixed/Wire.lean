module

public import Silmaril.Formats.Parquet.Int96.Mixed.Defs
import all Silmaril.Formats.Parquet.Int96.Mixed.Defs
public import Batteries.Data.List.Basic
import Silmaril.Formats.Parquet.Int96.Dictionary.Thms
import Silmaril.Formats.Parquet.Int96.Page.Thms
import Silmaril.Formats.Parquet.Page.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Int96.Mixed

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int96 Silmaril.Formats.Parquet.Int96.Mixed

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

theorem planData_sound {leaf : Footer.SchemaElement} {frame : Parquet.Page.Frame}
    {ordinal : Nat} {page : DataPage} (h : planData leaf frame ordinal = .ok page) :
    page.frame = frame ∧ page.ordinal = ordinal ∧
      Int96.Page.parameters leaf 0 frame.value = .ok page.params ∧
      page.params.encoding = (match page.encoding with | .plain => 0 | .dictionary => 8) := by
  unfold planData at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  obtain ⟨params, checked, h⟩ := bind_ok h
  have checked := mapError_ok checked
  split at h
  · rename_i tag
    cases h
    exact ⟨rfl, rfl, checked, tag⟩
  · split at h
    · rename_i tag
      cases h
      exact ⟨rfl, rfl, checked, tag⟩
    · contradiction

theorem decodePage_dispatch (limits : Dictionary.Limits) (policy : Policy) (source : Bytes)
    (leaf : Footer.SchemaElement) (dictionary : Array (Int96.Page.Value policy))
    {frame : Parquet.Page.Frame} {ordinal : Nat} {page : DataPage}
    (planned : planData leaf frame ordinal = .ok page) :
    decodePage limits policy source leaf dictionary page =
      if page.params.encoding = 0 then
        (Int96.Page.decode policy leaf 0 frame.value limits.scalar (Dictionary.frameBody source frame)).mapError
          (.page ordinal frame.header.start ∘ .plain)
      else
        (Dictionary.decodeData limits dictionary page.params (Dictionary.frameBody source frame)).mapError
          (.page ordinal frame.header.start ∘ .dictionary) := by
  obtain ⟨original, position, _, tag⟩ := planData_sound planned
  cases branch : page.encoding <;> simp [decodePage, original, position, branch, tag]

private theorem plain_count {policy : Policy} {leaf : Footer.SchemaElement} {frame : Parquet.Page.Frame}
    {limits : ScalarPage.Limits} {body : Bytes} {slots : Dictionary.Slots policy}
    {params : ScalarPage.Parameters} (checked : Int96.Page.parameters leaf 0 frame.value = .ok params)
    (decoded : Int96.Page.decode policy leaf 0 frame.value limits body = .ok slots) :
    slots.length = params.numValues := by
  have headerCount := (Int96.Page.parameters_sound checked).2.2.2.2.2
  have slotCount := Int96.Page.decode_counts decoded
  cases kind : frame.value.kind <;> simp only [kind] at headerCount slotCount
  · exact slotCount.trans headerCount.1.symm
  · exact slotCount.1.trans headerCount.1.symm

theorem decodePage_wire {limits : Dictionary.Limits} {policy : Policy} {source : Bytes}
    {leaf : Footer.SchemaElement} {dictionary : Array (Int96.Page.Value policy)}
    {frame : Parquet.Page.Frame} {ordinal : Nat} {page : DataPage} {slots : Dictionary.Slots policy}
    (planned : planData leaf frame ordinal = .ok page)
    (decoded : decodePage limits policy source leaf dictionary page = .ok slots) :
    DataWire limits source leaf dictionary frame slots ∧ slots.length = page.params.numValues := by
  obtain ⟨_, _, checked, tag⟩ := planData_sound planned
  rw [decodePage_dispatch limits policy source leaf dictionary planned] at decoded
  cases branch : page.encoding
  · have isPlain : page.params.encoding = 0 := by simpa [branch] using tag
    rw [ite_eq_left isPlain] at decoded
    have plain := mapError_ok decoded
    have count := plain_count checked plain
    exact ⟨⟨page.params, checked, count, Or.inl ⟨isPlain, plain⟩⟩, count⟩
  · have isDictionary : page.params.encoding = 8 := by simpa [branch] using tag
    rw [ite_eq_right (by simp [isDictionary])] at decoded
    have indexed := mapError_ok decoded
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, count⟩ := Dictionary.decodeData_wire indexed
    exact ⟨⟨page.params, checked, count, Or.inr ⟨isDictionary, indexed⟩⟩, count⟩

private theorem pages_ordered {limits : Dictionary.Limits} {policy : Policy} {source : Bytes}
    {leaf : Footer.SchemaElement} {dictionary : Array (Int96.Page.Value policy)}
    {frames : List (Parquet.Page.Frame × Nat)} {planned : List DataPage}
    {pages : List (Dictionary.Slots policy)}
    (plans : List.Forall₂ (fun entry item =>
      (planData leaf entry.1 entry.2).mapError (Cause.page entry.2 entry.1.header.start) = .ok item) frames planned)
    (decoded : List.Forall₂ (fun item slots =>
      decodePage limits policy source leaf dictionary item = .ok slots) planned pages) :
    List.Forall₂ (DataWire limits source leaf dictionary) (frames.map Prod.fst) pages ∧
      (pages.map List.length).sum = (planned.map (·.params.numValues)).sum := by
  induction plans generalizing pages with
  | nil =>
    cases decoded
    exact ⟨.nil, rfl⟩
  | cons chosen plannedTail ih =>
    cases decoded with
    | cons first tail =>
      have ⟨wire, pageCount⟩ := decodePage_wire (mapError_ok chosen) first
      have ⟨ordered, count⟩ := ih tail
      exact ⟨.cons wire ordered, by simp [pageCount, count]⟩

theorem read_wire {limits : Dictionary.Limits} {policy : Policy} {source : Bytes}
    {footerStart rowCount : Nat} {leaf : Footer.SchemaElement} {column : Footer.ColumnMetadata}
    {slots : Dictionary.Slots policy}
    (h : Mixed.read limits policy source footerStart rowCount leaf column = .ok slots) :
    ∃ span first rest header dictionary pages,
      Parquet.Page.columnSpan footerStart column = some span ∧
      Parquet.Page.readChunk limits.framing source span = .ok (first :: rest) ∧
      span.stop ≤ source.length ∧
      Parquet.Page.Chain span span.start span.stop (first :: rest) ∧
      column.dictionaryPageOffset = some (first.header.start : Int) ∧
      rest.head?.map (fun frame => (frame.header.start : Int)) = some column.dataPageOffset ∧
      first.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      Dictionary.readDictionary limits policy source first = .ok dictionary ∧
      List.Forall₂ (DataWire limits source leaf dictionary) rest pages ∧
      slots = pages.flatten ∧ slots.length = rowCount := by
  unfold Mixed.read at h
  have h := mapError_ok h
  unfold Mixed.read.readChunk at h
  obtain ⟨span, located, h⟩ := bind_ok h
  obtain ⟨frames, framed, h⟩ := bind_ok h
  have framed := mapError_ok framed
  cases frames with
  | nil => contradiction
  | cons first rest =>
    obtain ⟨dictionary, opened, h⟩ := bind_ok h
    cases rest with
    | nil => contradiction
    | cons data rest =>
      dsimp only at h
      split at h
      · contradiction
      · rename_i same
        have offset := not_ne_iff.mp same
        obtain ⟨planned, plannedOk, h⟩ := bind_ok h
        unfold plan at plannedOk
        split at h
        · contradiction
        · rename_i complete
          obtain ⟨pages, decoded, h⟩ := bind_ok h
          have opened := mapError_ok opened
          obtain ⟨header, _, kind, encoding, _⟩ := Dictionary.readDictionary_wire opened
          have ⟨ordered, count⟩ := pages_ordered (mapM_order _ plannedOk) (mapM_order _ decoded)
          have ⟨spanOk, dictionaryOffset⟩ := Dictionary.locate_span (mapError_ok located)
          have ⟨_, bounded, chain⟩ := Parquet.Page.readChunk_chain framed
          have firstAt {start stop : Nat} (walk : Parquet.Page.Chain span start stop (first :: data :: rest)) :
              first.header.start = start := by
            cases walk with
            | cons within _ => exact within.headerStart
          have result : pages.flatten = slots := Except.ok.inj h
          refine ⟨span, first, data :: rest, header, dictionary, pages, spanOk, framed, bounded, chain, ?_, by simp [offset],
            kind, encoding, opened, ?_, result.symm, ?_⟩
          · rw [firstAt chain]
            exact dictionaryOffset
          · simpa using ordered
          · rw [← result, List.length_flatten, count]
            exact not_ne_iff.mp complete

end Silmaril.Proofs.Formats.Parquet.Int96.Mixed
