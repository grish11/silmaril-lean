module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File.Defs
import Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File.Correctness
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Thms

/-! Checked admission and exact batches and errors for the tag-6 source. -/

public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File

open Silmaril.Relational Silmaril.Formats.Arrow

variable {limits : Limits} {input : Bytes} {int32Name byteArrayName : String}
variable {checked : Checked limits int32Name byteArrayName}

/-- A successful open binds the checked snapshot and its total row cap. -/
theorem openFile_snapshot (opened : openFile limits input int32Name byteArrayName = .ok checked) :
    Snapshot.check (Failure := Unit) limits.group.group.snapshot input = .ok checked.projection.snapshot ∧
    checked.projection.snapshot.metadata.numRows.toNat ≤ limits.maxFileRows :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File.openFile_snapshot opened

/-- An over-limit checked footer fails before a source can read any group. -/
theorem readAll_rowLimit
    {projection : Int32ByteArrayGroup.DeltaLength.Checked int32Name byteArrayName}
    (opened : Int32ByteArrayGroup.openFile limits.group.group input ⟨int32Name, .required⟩
      ⟨byteArrayName, .optional⟩ = .ok projection)
    (over : limits.maxFileRows < projection.snapshot.metadata.numRows.toNat) :
    Reader.readAll (openSource limits input int32Name byteArrayName) =
      .error (.openFailure (.fileRowLimit limits.maxFileRows projection.snapshot.metadata.numRows.toNat)) :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File.readAll_rowLimit opened over

/-- The exact trace is ordered by the original dense footer ordinals. -/
theorem readAll_trace (opened : openFile limits input int32Name byteArrayName = .ok checked) :
    let trace := Reader.denoteGroups (source checked).readGroup (List.range checked.projection.snapshot.groupCount)
    Reader.readAll (openSource limits input int32Name byteArrayName) =
      .ok ⟨schema int32Name byteArrayName, ⟨trace.1.map AlignedColumns.ofRows, trace.2⟩⟩ :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File.readAll_trace opened

/-- Every successful group contributes one batch, including an empty group. -/
theorem readAll_success {groups : List (List Int32ByteArrayGroup.Row)}
    (opened : openFile limits input int32Name byteArrayName = .ok checked)
    (decoded : (List.range checked.projection.snapshot.groupCount).mapM
      (Int32ByteArrayGroup.DeltaLength.readGroup checked.projection limits.group) = .ok groups) :
    Reader.readAll (openSource limits input int32Name byteArrayName) = .ok ⟨schema int32Name byteArrayName,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows int32Name byteArrayName), .eos⟩⟩ :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File.readAll_success opened decoded

/-- Earlier groups yield complete batches before the first original indexed error. -/
theorem readAll_first_error {before after : List Nat} {index : Nat}
    {groups : List (List Int32ByteArrayGroup.Row)} {reason : Int32ByteArrayGroup.DeltaLength.Error}
    (opened : openFile limits input int32Name byteArrayName = .ok checked)
    (split : List.range checked.projection.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Int32ByteArrayGroup.DeltaLength.readGroup checked.projection limits.group) = .ok groups)
    (failed : Int32ByteArrayGroup.DeltaLength.readGroup checked.projection limits.group index = .error reason) :
    Reader.readAll (openSource limits input int32Name byteArrayName) = .ok ⟨schema int32Name byteArrayName,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows int32Name byteArrayName), .readError (.groupFailure index reason)⟩⟩ :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File.readAll_first_error opened split earlier failed

/-- The emitted prefix is bounded by the admitted footer row cap. -/
theorem readAll_rows_le
    {selected : Scan.Schema String Kind} {trace : Events.Trace selected Value Error}
    (observed : Reader.readAll (openSource limits input int32Name byteArrayName) = .ok ⟨selected, trace⟩) :
    (trace.batches.map (·.rowCount)).sum ≤ limits.maxFileRows :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File.readAll_rows_le observed

/-- Batch materialization preserves both positional projections. -/
theorem batch_projections (int32Name byteArrayName : String) (pairs : List Int32ByteArrayGroup.Row) :
    let batch := AlignedColumns.ofRows (rows int32Name byteArrayName pairs)
    batch.rowCount = pairs.length ∧
    batch.values ⟨0, by change 0 < 2; decide⟩ = pairs.map Prod.fst ∧
    batch.values ⟨1, by change 1 < 2; decide⟩ = pairs.map Prod.snd :=
  Int32ByteArrayGroup.File.batch_projections ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩ pairs

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File
