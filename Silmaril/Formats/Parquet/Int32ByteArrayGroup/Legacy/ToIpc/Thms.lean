module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Correctness

public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc

open Silmaril.Formats.Arrow.MixedFlat Silmaril.Relational
open Int32ByteArrayGroup (Row)

variable {parquet : Legacy.Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes}
variable {int32Name byteArrayName : String} {wire : KBytes}
variable {checked : Legacy.Checked parquet int32Name byteArrayName}

/-- Native readback preserves the checked source fields, each complete batch,
the exact opaque octets, and EOS at the end of the carrier. -/
theorem convert_readback (written : convert parquet ipc input int32Name byteArrayName = .ok wire) :
    ∃ (checked : Legacy.Checked parquet int32Name byteArrayName)
      (groups : List (List Row)) (decoded : Stream.Observed),
      Legacy.openFile parquet input int32Name byteArrayName = .ok checked ∧
      List.Forall₂ (fun index pairs => Legacy.readGroup checked index = .ok pairs)
        (List.range checked.projection.snapshot.groupCount) groups ∧
      Legacy.readAll parquet input int32Name byteArrayName =
        .ok ⟨Legacy.schema int32Name byteArrayName,
          ⟨groups.map (AlignedColumns.ofRows ∘ Legacy.rows int32Name byteArrayName), .eos⟩⟩ ∧
      Stream.read ipc wire = .ok decoded ∧
      decoded.fields = [⟨int32Name, false, .primitive .int32⟩, ⟨byteArrayName, true, .view .binary⟩] ∧
      decoded.batches.map StreamWriter.observeBatch =
        groups.map (Int32ByteArrayGroup.ToIpc.groupObservation ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩) ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.convert_readback written

/-- A late source error retains its original payload and yields no IPC stream. -/
theorem convert_first_error {before after : List Nat} {index : Nat}
    {groups : List (List Row)} {cause : Legacy.Error}
    (opened : Legacy.openFile parquet input int32Name byteArrayName = .ok checked)
    (split : List.range checked.projection.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i pairs => Legacy.readGroup checked i = .ok pairs) before groups)
    (failed : Legacy.readGroup checked index = .error cause) :
    convert parquet ipc input int32Name byteArrayName = .error (.source cause) :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.convert_first_error opened split earlier failed

/-- Source admission is checked before the writer. -/
theorem convert_open_error {cause : Legacy.Error}
    (failed : Legacy.openFile parquet input int32Name byteArrayName = .error cause) :
    convert parquet ipc input int32Name byteArrayName = .error (.source cause) := by
  simp [convert, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc
