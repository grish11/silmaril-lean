module

public import Silmaril.Formats.Parquet.Int96.Mixed.File.Defs
import all Silmaril.Formats.Parquet.Int96.Mixed.File.Defs
public import Batteries.Data.List.Basic
import Silmaril.Formats.Parquet.Int96.Dictionary.File.Thms
import Silmaril.Formats.Parquet.Int96.Mixed.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Int96.Mixed.File

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int96 Silmaril.Formats.Parquet.Int96.Mixed.File

variable {name : String} {layout : FlatColumn.Layout} {interpretation : Policy}

theorem openFile_binding {limits : Limits} {source : Bytes} {checked : Checked name layout interpretation}
    (opened : openFile limits source name layout interpretation = .ok checked) :
    Dictionary.File.openFile limits source name layout interpretation = .ok checked.selection := by
  cases selected : Dictionary.File.openFile limits source name layout interpretation with
  | error cause => simp [openFile, selected, Except.map] at opened
  | ok selection =>
    simp [openFile, selected, Except.map] at opened
    cases opened
    rfl

theorem openFile_snapshot {limits : Limits} {source : Bytes} {checked : Checked name layout interpretation}
    (opened : openFile limits source name layout interpretation = .ok checked) :
    source.length ≤ limits.maxFileBytes ∧
      Snapshot.check (Failure := Unit) limits.snapshot source = .ok checked.selection.bound.snapshot ∧
      checked.selection.bound.snapshot.metadata.numRows.toNat ≤ limits.maxTotalRows ∧
      FlatColumn.bindColumn checked.selection.bound.snapshot ⟨name, .int96, layout⟩ =
        .ok checked.selection.bound.binding :=
  Dictionary.File.openFile_snapshot (openFile_binding opened)

theorem openFile_disjoint {limits : Limits} {source : Bytes} {checked : Checked name layout interpretation}
    (opened : openFile limits source name layout interpretation = .ok checked) :
    ∃ ranges : List (Nat × Footer.Span),
      ranges.Pairwise (fun left right => left.2.stop ≤ right.2.start ∨ right.2.stop ≤ left.2.start) ∧
      ∀ index < checked.selection.bound.snapshot.groupCount, ∃ selected,
        Dictionary.File.select checked.selection.bound index = .ok selected ∧
          ranges[index]? = some (index, selected.span) :=
  Dictionary.File.openFile_disjoint (openFile_binding opened)

theorem readGroup_of_selected (checked : Checked name layout interpretation) {index : Nat}
    {selected : Dictionary.File.Selected} (chosen : Dictionary.File.select checked.selection.bound index = .ok selected) :
    checked.readGroup index =
      (Mixed.read checked.selection.chunkLimits interpretation checked.selection.bound.snapshot.bytes
        checked.selection.bound.snapshot.footer.start selected.group.numRows.toNat
        checked.selection.bound.binding.leaf selected.column.metadata).mapError
          (.chunk index checked.selection.bound.binding.columnOrdinal name) := by
  simp [Checked.readGroup, chosen, Bind.bind, Except.bind, Except.mapError]

theorem readGroup_wire {checked : Checked name layout interpretation} {index : Nat}
    {slots : Dictionary.Slots interpretation} (decoded : checked.readGroup index = .ok slots) :
    let bound := checked.selection.bound
    let limits := checked.selection.chunkLimits
    ∃ selected first rest header dictionary pages,
      Dictionary.File.select bound index = .ok selected ∧
      bound.snapshot.metadata.schema[bound.binding.leafOrdinal]? = some bound.binding.leaf ∧
      bound.snapshot.groupAt index = some selected.group ∧
      selected.group.columns[bound.binding.columnOrdinal]? = some selected.column ∧
      Parquet.Page.readChunk limits.framing bound.snapshot.bytes selected.span = .ok (first :: rest) ∧
      selected.span.stop ≤ bound.snapshot.bytes.length ∧
      Parquet.Page.Chain selected.span selected.span.start selected.span.stop (first :: rest) ∧
      selected.column.metadata.dictionaryPageOffset = some (first.header.start : Int) ∧
      rest.head?.map (fun frame => (frame.header.start : Int)) = some selected.column.metadata.dataPageOffset ∧
      first.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      Dictionary.readDictionary limits interpretation bound.snapshot.bytes first = .ok dictionary ∧
      List.Forall₂ (Mixed.DataWire limits bound.snapshot.bytes bound.binding.leaf dictionary) rest pages ∧
      slots = pages.flatten ∧ slots.length = selected.group.numRows.toNat := by
  cases chosen : Dictionary.File.select checked.selection.bound index with
  | error cause => simp [Checked.readGroup, chosen, Bind.bind, Except.bind, Except.mapError] at decoded
  | ok selected =>
    rw [readGroup_of_selected checked chosen] at decoded
    have physical : Mixed.read checked.selection.chunkLimits interpretation checked.selection.bound.snapshot.bytes
        checked.selection.bound.snapshot.footer.start selected.group.numRows.toNat
        checked.selection.bound.binding.leaf selected.column.metadata = .ok slots := by
      unfold Except.mapError at decoded
      split at decoded <;> rename_i result read
      · contradiction
      · cases decoded
        exact read
    obtain ⟨span, first, rest, header, dictionary, pages, slice, framed, bounded, chain, dictOffset,
      dataOffset, kind, encoding, dictionaryOk, ordered, flattened, count⟩ := Mixed.read_wire physical
    obtain ⟨group, column, _, _, _, spanOk⟩ := Dictionary.File.select_sound chosen
    have sameSpan : span = selected.span := Option.some.inj (slice.symm.trans spanOk)
    exact ⟨selected, first, rest, header, dictionary, pages, chosen, checked.selection.bound.binding.leafAt,
      group, column, sameSpan ▸ framed, sameSpan ▸ bounded, sameSpan ▸ chain,
      dictOffset, dataOffset, kind, encoding, dictionaryOk, ordered, flattened, count⟩

private theorem collect_cons (checked : Checked name layout interpretation) (index : Nat)
    (rest : List Nat) (reversed : List (Dictionary.Slots interpretation)) :
    collect checked (index :: rest) reversed =
      match checked.readGroup index with
      | .ok slots => collect checked rest (slots :: reversed)
      | .error cause => ⟨reversed.reverse, some cause⟩ := by
  unfold collect
  rw [List.foldlM_cons]
  unfold step
  cases checked.readGroup index <;> rfl

private theorem collect_sound (checked : Checked name layout interpretation)
    (indices : List Nat) (reversed : List (Dictionary.Slots interpretation)) :
    let trace := collect checked indices reversed
    ∃ completed, trace.groups = reversed.reverse ++ completed ∧
      match trace.failure with
      | none => indices.mapM checked.readGroup = .ok completed
      | some cause =>
        ∃ before index after, indices = before ++ index :: after ∧
          before.mapM checked.readGroup = .ok completed ∧ checked.readGroup index = .error cause := by
  induction indices generalizing reversed with
  | nil => exact ⟨[], by simp [collect, Pure.pure, Except.pure], rfl⟩
  | cons index rest ih =>
    dsimp only
    rw [collect_cons]
    cases first : checked.readGroup index with
    | error cause => exact ⟨[], by simp, [], index, rest, rfl, rfl, first⟩
    | ok slots =>
      obtain ⟨completed, ordered, outcome⟩ := ih (slots :: reversed)
      refine ⟨slots :: completed, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using ordered
      · cases failed : (collect checked rest (slots :: reversed)).failure with
        | none =>
          simp only [failed] at outcome ⊢
          simp [List.mapM_cons, first, outcome, Bind.bind, Except.bind, Pure.pure, Except.pure]
        | some cause =>
          simp only [failed] at outcome ⊢
          obtain ⟨before, bad, after, rfl, earlier, invalid⟩ := outcome
          refine ⟨index :: before, bad, after, rfl, ?_, invalid⟩
          simp [List.mapM_cons, first, earlier, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem readAll_sound (checked : Checked name layout interpretation) :
    let indices := List.range checked.selection.bound.snapshot.groupCount
    let trace := checked.readAll
    match trace.failure with
    | none => indices.mapM checked.readGroup = .ok trace.groups
    | some cause =>
      ∃ before index after, indices = before ++ index :: after ∧
        before.mapM checked.readGroup = .ok trace.groups ∧ checked.readGroup index = .error cause := by
  obtain ⟨completed, ordered, outcome⟩ :=
    collect_sound checked (List.range checked.selection.bound.snapshot.groupCount) []
  simp only [List.reverse_nil, List.nil_append] at ordered
  cases failed : (collect checked (List.range checked.selection.bound.snapshot.groupCount) []).failure <;>
    simpa only [Checked.readAll, ordered, failed] using outcome

end Silmaril.Proofs.Formats.Parquet.Int96.Mixed.File
