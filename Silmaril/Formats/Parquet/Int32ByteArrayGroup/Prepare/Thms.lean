module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Prepare.Defs
import Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.Prepare.Correctness

public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.Prepare

open Silmaril.Relational

variable {limits : File.Limits} {input : Bytes} {int32 byteArray : Field}
variable {checked : File.Checked limits int32 byteArray}

/-- Each prepared group retains all paired nullable slots. The byte-tree
carrier represents the same opaque octets. -/
theorem batch_values (int32 byteArray : Field) (pairs : List Row) :
    let batch := Batch.ofRows int32 byteArray (File.rows int32 byteArray pairs)
    batch.rowCount = pairs.length ∧ batch.intValues = pairs.map Prod.fst ∧
      batch.viewValues.map (Option.map KBytes.toList) =
        pairs.map (fun pair => pair.2.map Bytes.toList) :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.Prepare.batch_values int32 byteArray pairs

/-- Preparation succeeds exactly after a checked open and successful reads of
every footer group, with the specified schema and one prepared batch per read. -/
theorem prepare_ok_iff {result : Prepared} :
    prepare limits input int32 byteArray = .ok result ↔
      ∃ checked : File.Checked limits int32 byteArray, File.openFile limits input int32 byteArray = .ok checked ∧
        ∃ groups, (List.range checked.projection.snapshot.groupCount).mapM
          (checked.projection.readGroup limits.group) = .ok groups ∧
          result = ⟨Schema.ofSelection int32 byteArray,
            groups.map (Batch.ofRows int32 byteArray ∘ File.rows int32 byteArray)⟩ :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.Prepare.prepare_ok_iff

/-- The exact ordered Arrow descriptors and one paired batch per footer group.
An empty group retains its position and has zero rows in both columns. -/
theorem prepare_exact {result : Prepared} (success : prepare limits input int32 byteArray = .ok result) :
    ∃ (checked : File.Checked limits int32 byteArray) (groups : List (List Row)),
      File.openFile limits input int32 byteArray = .ok checked ∧
      (List.range checked.projection.snapshot.groupCount).mapM
        (checked.projection.readGroup limits.group) = .ok groups ∧
      result.schema.fields = [⟨int32.name, decide (int32.layout = .optional), .primitive .int32⟩,
        ⟨byteArray.name, decide (byteArray.layout = .optional), .view .binary⟩] ∧
      result.batches.length = checked.projection.snapshot.groupCount ∧
      List.Forall₂ (fun (batch : Batch) pairs => batch.rowCount = pairs.length ∧
        batch.intValues = pairs.map Prod.fst ∧ batch.viewValues.map (Option.map KBytes.toList) =
          pairs.map (fun pair => pair.2.map Bytes.toList)) result.batches groups :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.Prepare.prepare_exact success

/-- An admission failure, including a whole-file row cap failure, is unchanged. -/
theorem prepare_open_error {cause : File.Error}
    (failed : File.openFile limits input int32 byteArray = .error cause) :
    prepare limits input int32 byteArray = .error cause := by
  simp [prepare, failed, Bind.bind, Except.bind]

/-- Preparation returns the original indexed failure without a result.
The separately consumed source keeps the complete prefix. -/
theorem prepare_first_error {before after : List Nat} {index : Nat} {groups : List (List Row)}
    {reason : Int32ByteArrayGroup.Error}
    (opened : File.openFile limits input int32 byteArray = .ok checked)
    (split : List.range checked.projection.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.projection.readGroup limits.group) = .ok groups)
    (failed : checked.projection.readGroup limits.group index = .error reason) :
    prepare limits input int32 byteArray = .error (.groupFailure index reason) ∧
      Reader.readAll (File.openSource limits input int32 byteArray) = .ok
        ⟨File.schema int32 byteArray,
          ⟨groups.map (AlignedColumns.ofRows ∘ File.rows int32 byteArray), .readError (.groupFailure index reason)⟩⟩ :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.Prepare.prepare_first_error opened split earlier failed

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.Prepare
