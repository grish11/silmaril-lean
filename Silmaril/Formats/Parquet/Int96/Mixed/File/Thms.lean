module

public import Silmaril.Formats.Parquet.Int96.Mixed.File.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Int96.Mixed.File.Read

public section

namespace Silmaril.Formats.Parquet.Int96.Mixed.File

variable {name : String} {layout : FlatColumn.Layout} {interpretation : Policy}

/-- Opening retains the original checked selected-leaf capability. -/
theorem openFile_binding {limits : Limits} {source : Bytes} {checked : Checked name layout interpretation}
    (opened : openFile limits source name layout interpretation = .ok checked) :
    Dictionary.File.openFile limits source name layout interpretation = .ok checked.selection :=
  Proofs.Formats.Parquet.Int96.Mixed.File.openFile_binding opened

/-- The selected leaf belongs to the exact checked source and bounded footer count. -/
theorem openFile_snapshot {limits : Limits} {source : Bytes} {checked : Checked name layout interpretation}
    (opened : openFile limits source name layout interpretation = .ok checked) :
    source.length ≤ limits.maxFileBytes ∧
      Snapshot.check (Failure := Unit) limits.snapshot source = .ok checked.selection.bound.snapshot ∧
      checked.selection.bound.snapshot.metadata.numRows.toNat ≤ limits.maxTotalRows ∧
      FlatColumn.bindColumn checked.selection.bound.snapshot ⟨name, .int96, layout⟩ =
        .ok checked.selection.bound.binding :=
  Proofs.Formats.Parquet.Int96.Mixed.File.openFile_snapshot opened

/-- The preflight catalogue contains the original span at each footer index,
and spans are pairwise disjoint. -/
theorem openFile_disjoint {limits : Limits} {source : Bytes} {checked : Checked name layout interpretation}
    (opened : openFile limits source name layout interpretation = .ok checked) :
    ∃ ranges : List (Nat × Footer.Span),
      ranges.Pairwise (fun left right => left.2.stop ≤ right.2.start ∨ right.2.stop ≤ left.2.start) ∧
      ∀ index < checked.selection.bound.snapshot.groupCount, ∃ selected,
        Dictionary.File.select checked.selection.bound index = .ok selected ∧
          ranges[index]? = some (index, selected.span) :=
  Proofs.Formats.Parquet.Int96.Mixed.File.openFile_disjoint opened

/-- The selected mixed chunk decoder receives the original source and metadata.
The error wrapper adds the exact group, column and name. -/
theorem readGroup_of_selected (checked : Checked name layout interpretation) {index : Nat}
    {selected : Dictionary.File.Selected} (chosen : Dictionary.File.select checked.selection.bound index = .ok selected) :
    checked.readGroup index =
      (Mixed.read checked.selection.chunkLimits interpretation checked.selection.bound.snapshot.bytes
        checked.selection.bound.snapshot.footer.start selected.group.numRows.toNat
        checked.selection.bound.binding.leaf selected.column.metadata).mapError
          (.chunk index checked.selection.bound.binding.columnOrdinal name) :=
  Proofs.Formats.Parquet.Int96.Mixed.File.readGroup_of_selected checked chosen

/-- A successful group read retains its original leaf, chunk, frames, and
row count. Each data frame denotes the slots of its checked decoder. -/
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
      slots = pages.flatten ∧ slots.length = selected.group.numRows.toNat :=
  Proofs.Formats.Parquet.Int96.Mixed.File.readGroup_wire decoded

/-- Collection follows exact footer order. A failed group publishes only
the preceding complete groups and returns its original read error. -/
theorem readAll_sound (checked : Checked name layout interpretation) :
    let indices := List.range checked.selection.bound.snapshot.groupCount
    let trace := checked.readAll
    match trace.failure with
    | none => indices.mapM checked.readGroup = .ok trace.groups
    | some cause =>
      ∃ before index after, indices = before ++ index :: after ∧
        before.mapM checked.readGroup = .ok trace.groups ∧ checked.readGroup index = .error cause :=
  Proofs.Formats.Parquet.Int96.Mixed.File.readAll_sound checked

end Silmaril.Formats.Parquet.Int96.Mixed.File
