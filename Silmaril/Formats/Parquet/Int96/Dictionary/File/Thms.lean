module

public import Silmaril.Formats.Parquet.Int96.Dictionary.File.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Int96.Dictionary.File.Read

public section

namespace Silmaril.Formats.Parquet.Int96.Dictionary.File

variable {name : String} {layout : FlatColumn.Layout} {interpretation : Policy}

/-- Selection refers to the exact footer group and bound column, with matching
path, physical type, declared count and interval. -/
theorem select_sound {bound : Int96.File.Checked name layout interpretation}
    {index : Nat} {selected : Selected} (h : select bound index = .ok selected) :
    bound.snapshot.groupAt index = some selected.group ∧
      selected.group.columns[bound.binding.columnOrdinal]? = some selected.column ∧
      selected.column.metadata.pathInSchema = [bound.binding.leaf.name] ∧
      selected.column.metadata.physicalType = .int96 ∧
      selected.column.metadata.numValues = selected.group.numRows ∧
      Parquet.Page.columnSpan bound.snapshot.footer.start selected.column.metadata = some selected.span :=
  Proofs.Formats.Parquet.Int96.Dictionary.File.select_sound h

/-- Every selected footer ordinal has its original span in the preflight
catalogue, and those spans are pairwise disjoint. -/
theorem openFile_disjoint {limits : Limits} {source : Bytes} {checked : Checked name layout interpretation}
    (accepted : openFile limits source name layout interpretation = .ok checked) :
    ∃ ranges : List (Nat × Footer.Span),
      ranges.Pairwise (fun left right => left.2.stop ≤ right.2.start ∨ right.2.stop ≤ left.2.start) ∧
      ∀ index < checked.bound.snapshot.groupCount, ∃ selected,
        select checked.bound index = .ok selected ∧ ranges[index]? = some (index, selected.span) :=
  Proofs.Formats.Parquet.Int96.Dictionary.File.openFile_disjoint accepted

/-- Opening uses the caller’s bytes and checks the bounded snapshot and flat
leaf before any group read. -/
theorem openFile_snapshot {limits : Limits} {source : Bytes} {checked : Checked name layout interpretation}
    (accepted : openFile limits source name layout interpretation = .ok checked) :
    source.length ≤ limits.maxFileBytes ∧
      Snapshot.check (Failure := Unit) limits.snapshot source = .ok checked.bound.snapshot ∧
      checked.bound.snapshot.metadata.numRows.toNat ≤ limits.maxTotalRows ∧
      FlatColumn.bindColumn checked.bound.snapshot ⟨name, .int96, layout⟩ = .ok checked.bound.binding :=
  Proofs.Formats.Parquet.Int96.Dictionary.File.openFile_snapshot accepted

/-- The selected chunk decoder receives the retained bytes and original
metadata. A failure gains the group and column coordinates. -/
theorem readGroup_of_selected (checked : Checked name layout interpretation) {index : Nat}
    {selected : Selected} (h : select checked.bound index = .ok selected) :
    checked.readGroup index =
      (Dictionary.read checked.chunkLimits interpretation checked.bound.snapshot.bytes
        checked.bound.snapshot.footer.start selected.group.numRows.toNat checked.bound.binding.leaf
        selected.column.metadata).mapError
          (.chunk index checked.bound.binding.columnOrdinal name) :=
  Proofs.Formats.Parquet.Int96.Dictionary.File.readGroup_of_selected checked h

/-- The original source yields the exact dictionary and data frames. Group
slots are the ordered page results at the footer row count. -/
theorem readGroup_wire {checked : Checked name layout interpretation} {index : Nat}
    {slots : Slots interpretation} (decoded : checked.readGroup index = .ok slots) :
    ∃ selected first rest dictionary pages,
      select checked.bound index = .ok selected ∧
      checked.bound.snapshot.metadata.schema[checked.bound.binding.leafOrdinal]? =
        some checked.bound.binding.leaf ∧
      checked.bound.snapshot.groupAt index = some selected.group ∧
      selected.group.columns[checked.bound.binding.columnOrdinal]? = some selected.column ∧
      Parquet.Page.readChunk checked.chunkLimits.framing checked.bound.snapshot.bytes selected.span =
        .ok (first :: rest) ∧
      Parquet.Page.Chain selected.span selected.span.start selected.span.stop (first :: rest) ∧
      selected.column.metadata.dictionaryPageOffset = some (first.header.start : Int) ∧
      rest.head?.map (fun frame => (frame.header.start : Int)) = some selected.column.metadata.dataPageOffset ∧
      Dictionary.readDictionary checked.chunkLimits interpretation checked.bound.snapshot.bytes first =
        .ok dictionary ∧
      List.Forall₂ (fun frame page => ∃ params,
        Dictionary.dataParameters checked.bound.binding.leaf frame.value = .ok params ∧
        Dictionary.decodeData checked.chunkLimits dictionary params
          (Dictionary.frameBody checked.bound.snapshot.bytes frame) = .ok page) rest pages ∧
      slots = pages.flatten ∧ slots.length = selected.group.numRows.toNat :=
  Proofs.Formats.Parquet.Int96.Dictionary.File.readGroup_wire decoded

/-- Collection either completes every footer ordinal or returns the exact
completed prefix and first read error. -/
theorem readAll_sound (checked : Checked name layout interpretation) :
    let indices := List.range checked.bound.snapshot.groupCount
    let trace := checked.readAll
    match trace.failure with
    | none => indices.mapM checked.readGroup = .ok trace.groups
    | some cause =>
      ∃ before index after, indices = before ++ index :: after ∧
        before.mapM checked.readGroup = .ok trace.groups ∧ checked.readGroup index = .error cause :=
  Proofs.Formats.Parquet.Int96.Dictionary.File.readAll_sound checked

/-- Successful reads of every footer ordinal yield the complete trace. -/
theorem readAll_complete {checked : Checked name layout interpretation} {groups : List (Slots interpretation)}
    (decoded : (List.range checked.bound.snapshot.groupCount).mapM checked.readGroup = .ok groups) :
    checked.readAll = ⟨groups, none⟩ :=
  Proofs.Formats.Parquet.Int96.Dictionary.File.readAll_complete decoded

/-- The first failed group contributes no rows and determines the terminal
cause independently of later groups. -/
theorem readAll_first_error {checked : Checked name layout interpretation}
    {before after : List Nat} {index : Nat} {groups : List (Slots interpretation)} {cause : ReadError}
    (split : List.range checked.bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM checked.readGroup = .ok groups)
    (failed : checked.readGroup index = .error cause) :
    checked.readAll = ⟨groups, some cause⟩ :=
  Proofs.Formats.Parquet.Int96.Dictionary.File.readAll_first_error split earlier failed

end Silmaril.Formats.Parquet.Int96.Dictionary.File
