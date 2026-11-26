module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.Defs
import Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.Correctness

public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy

open Silmaril.Formats.Arrow Silmaril.Relational

variable {limits : Limits} {input : Bytes} {int32Name byteArrayName : String}
variable {checked : Checked limits int32Name byteArrayName}

/-- Open establishes the shared checked snapshot and the total row cap. -/
theorem openFile_snapshot (opened : openFile limits input int32Name byteArrayName = .ok checked) :
    Snapshot.check (Failure := Unit) limits.file.group.snapshot input = .ok checked.projection.snapshot ∧
    checked.projection.snapshot.metadata.numRows.toNat ≤ limits.file.maxFileRows :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.openFile_snapshot opened

/-- Both leaves use their original chunks in the same checked footer group. -/
theorem readGroup_wire {index : Nat} {pairs : List Int32ByteArrayGroup.Row}
    (read : readGroup checked index = .ok pairs) : GroupWire checked index pairs :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.readGroup_wire read

/-- The source trace follows the original indexed footer groups. -/
theorem readAll_order (opened : openFile limits input int32Name byteArrayName = .ok checked) :
    let trace := Reader.denoteGroups (rowsAt checked) (List.range checked.projection.snapshot.groupCount)
    readAll limits input int32Name byteArrayName = .ok ⟨schema int32Name byteArrayName,
      ⟨trace.1.map AlignedColumns.ofRows, trace.2⟩⟩ :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.readAll_order opened

/-- Every complete paired group contributes one batch, including an empty group. -/
theorem readAll_success {groups : List (List Int32ByteArrayGroup.Row)}
    (opened : openFile limits input int32Name byteArrayName = .ok checked)
    (decoded : List.Forall₂ (fun index pairs => readGroup checked index = .ok pairs)
      (List.range checked.projection.snapshot.groupCount) groups) :
    readAll limits input int32Name byteArrayName = .ok ⟨schema int32Name byteArrayName,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows int32Name byteArrayName), .eos⟩⟩ :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.readAll_success opened decoded

/-- The first original indexed error retains exactly the preceding complete batches. -/
theorem readAll_first_error {before after : List Nat} {index : Nat}
    {groups : List (List Int32ByteArrayGroup.Row)} {cause : Error}
    (opened : openFile limits input int32Name byteArrayName = .ok checked)
    (split : List.range checked.projection.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i pairs => readGroup checked i = .ok pairs) before groups)
    (failed : readGroup checked index = .error cause) :
    readAll limits input int32Name byteArrayName = .ok ⟨schema int32Name byteArrayName,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows int32Name byteArrayName), .readError cause⟩⟩ :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.readAll_first_error opened split earlier failed

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy
