module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Defs
import Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.File.Correctness

/-! Checked open and exact complete batches up to the first indexed error. -/

public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.File

open Silmaril.Relational Silmaril.Formats.Arrow

theorem openFile_snapshot {limits : Limits} {input : Bytes} {int32 byteArray : Field}
    {checked : Checked limits int32 byteArray} (opened : openFile limits input int32 byteArray = .ok checked) :
    Snapshot.check (Failure := Unit) limits.group.snapshot input = .ok checked.projection.snapshot ∧
    checked.projection.snapshot.metadata.numRows.toNat ≤ limits.maxFileRows :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.File.openFile_snapshot opened

/-- Each batch keeps both exact projections, even for an empty group. -/
theorem batch_projections (int32 byteArray : Field) (pairs : List Int32ByteArrayGroup.Row) :
    let batch := AlignedColumns.ofRows (rows int32 byteArray pairs)
    batch.rowCount = pairs.length ∧
    batch.values ⟨0, by change 0 < 2; decide⟩ = pairs.map Prod.fst ∧
    batch.values ⟨1, by change 1 < 2; decide⟩ = pairs.map Prod.snd :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.File.batch_projections int32 byteArray pairs

/-- Successful consumption keeps one batch for each footer ordinal. -/
theorem readAll_success {limits : Limits} {input : Bytes} {int32 byteArray : Field}
    {checked : Checked limits int32 byteArray} {groups : List (List Int32ByteArrayGroup.Row)}
    (opened : openFile limits input int32 byteArray = .ok checked)
    (decoded : (List.range checked.projection.snapshot.groupCount).mapM
      (checked.projection.readGroup limits.group) = .ok groups) :
    Reader.readAll (openSource limits input int32 byteArray) = .ok ⟨schema int32 byteArray,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows int32 byteArray), .eos⟩⟩ :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.File.readAll_success opened decoded

/-- The original failed group's cause determines the terminal outcome.
Every successful earlier group contributes its complete batch. -/
theorem readAll_first_error {limits : Limits} {input : Bytes} {int32 byteArray : Field}
    {checked : Checked limits int32 byteArray} {before after : List Nat} {index : Nat}
    {groups : List (List Int32ByteArrayGroup.Row)} {reason : Int32ByteArrayGroup.Error}
    (opened : openFile limits input int32 byteArray = .ok checked)
    (split : List.range checked.projection.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.projection.readGroup limits.group) = .ok groups)
    (failed : checked.projection.readGroup limits.group index = .error reason) :
    Reader.readAll (openSource limits input int32 byteArray) = .ok ⟨schema int32 byteArray,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows int32 byteArray), .readError (.groupFailure index reason)⟩⟩ :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.File.readAll_first_error opened split earlier failed

/-- The complete emitted prefix, whether followed by EOS or a read error,
cannot exceed the admitted file row limit. -/
theorem readAll_rows_le {limits : Limits} {input : Bytes} {int32 byteArray : Field}
    {selected : Scan.Schema String Kind} {trace : Events.Trace selected Value Error}
    (observed : Reader.readAll (openSource limits input int32 byteArray) = .ok ⟨selected, trace⟩) :
    (trace.batches.map (·.rowCount)).sum ≤ limits.maxFileRows :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.File.readAll_rows_le observed

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.File
