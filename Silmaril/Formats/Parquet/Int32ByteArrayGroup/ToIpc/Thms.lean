module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Prepare.Thms
import Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Correctness

public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc

open Silmaril.Relational
open Arrow.MixedFlat

variable {parquet : File.Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes}
variable {int32 byteArray : Field} {wire : KBytes}

/-- The mixed IPC batch input records the same paired slots as the typed source rows. -/
theorem writerBatch_ofRows_observe (int32 byteArray : Field) (pairs : List Row) :
    (writerBatch (Prepare.Batch.ofRows int32 byteArray (File.rows int32 byteArray pairs))).observe
        (writerSchema (Prepare.Schema.ofSelection int32 byteArray)) =
      groupObservation int32 byteArray pairs :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.ToIpc.writerBatch_ofRows_observe int32 byteArray pairs

/-- Success consists of complete source preparation and successful native emission. -/
theorem convert_ok_iff :
    convert parquet ipc input int32 byteArray = .ok wire ↔
      ∃ prepared, Prepare.prepare parquet input int32 byteArray = .ok prepared ∧
        StreamWriter.emit ipc (writerSchema prepared.schema) (prepared.batches.map writerBatch) = .ok wire :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.ToIpc.convert_ok_iff

/-- The native stream retains exact INT32-first descriptors and paired slots
within every original footer group and consumes the carrier through exact EOS. -/
theorem convert_readback (written : convert parquet ipc input int32 byteArray = .ok wire) :
    ∃ (checked : File.Checked parquet int32 byteArray) (groups : List (List Row)) (decoded : Stream.Observed),
      File.openFile parquet input int32 byteArray = .ok checked ∧
      (List.range checked.projection.snapshot.groupCount).mapM
        (checked.projection.readGroup parquet.group) = .ok groups ∧
      Stream.read ipc wire = .ok decoded ∧
      decoded.fields = (Prepare.Schema.ofSelection int32 byteArray).fields ∧
      decoded.batches.map StreamWriter.observeBatch = groups.map (groupObservation int32 byteArray) ∧
      decoded.batches.map (fun batch => batch.observed.rowCount) = groups.map List.length ∧
      decoded.batches.length = checked.projection.snapshot.groupCount ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.ToIpc.convert_readback written

/-- An open-time source refusal has priority over writer errors. -/
theorem convert_open_error {cause : File.Error}
    (failed : File.openFile parquet input int32 byteArray = .error cause) :
    convert parquet ipc input int32 byteArray = .error (.source cause) := by
  simp [convert, Prepare.prepare_open_error failed, Except.mapError, Bind.bind, Except.bind]

/-- No completed wire is returned after a late source failure. The separate
checked trace retains the successful prefix, including empty groups. -/
theorem convert_first_error {checked : File.Checked parquet int32 byteArray}
    {before after : List Nat} {index : Nat} {groups : List (List Row)} {reason : Int32ByteArrayGroup.Error}
    (opened : File.openFile parquet input int32 byteArray = .ok checked)
    (split : List.range checked.projection.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.projection.readGroup parquet.group) = .ok groups)
    (failed : checked.projection.readGroup parquet.group index = .error reason) :
    convert parquet ipc input int32 byteArray = .error (.source (.groupFailure index reason)) ∧
      Reader.readAll (File.openSource parquet input int32 byteArray) = .ok
        ⟨File.schema int32 byteArray,
          ⟨groups.map (AlignedColumns.ofRows ∘ File.rows int32 byteArray), .readError (.groupFailure index reason)⟩⟩ := by
  obtain ⟨error, trace⟩ := Prepare.prepare_first_error opened split earlier failed
  exact ⟨by simp [convert, error, Except.mapError, Bind.bind, Except.bind], trace⟩

/-- After complete source preparation, preserve the writer's original failure. -/
theorem convert_writer_error {prepared : Prepare.Prepared} {cause : StreamWriter.Error}
    (finished : Prepare.prepare parquet input int32 byteArray = .ok prepared)
    (failed : StreamWriter.emit ipc (writerSchema prepared.schema) (prepared.batches.map writerBatch) = .error cause) :
    convert parquet ipc input int32 byteArray = .error (.writer cause) := by
  simp [convert, finished, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc
