module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan.Defs
import Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan.Correctness

public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan

open Silmaril.Relational Arrow.MixedFlat

variable {parquet : Legacy.Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes}
variable {int32Name byteArrayName : String} {project : Projection} {keep : Predicate} {wire : KBytes}
variable {checked : Legacy.Checked parquet int32Name byteArrayName}

/-- Ordered preparation preserves the exact projected labels and nullable
slots, including repeated fields and row counts at width zero. -/
theorem orderedBatch_exact {selected : Schema} (batch : Batch selected) :
    (orderedBatch batch).fields = fields selected ∧ (orderedBatch batch).observe = observe batch :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan.orderedBatch_exact batch

/-- The native stream reads back with the precise projected fields and ordered
column observations from each successful footer group. Its explicit batch
counts include zero-width and zero-row batches, and framing ends at exact EOS. -/
theorem convert_readback
    (written : convert parquet ipc input int32Name byteArrayName project keep = .ok wire) :
    ∃ (checked : Legacy.Checked parquet int32Name byteArrayName) (decoded : Stream.Observed),
      Legacy.openFile parquet input int32Name byteArrayName = .ok checked ∧
      let selected := Legacy.schema int32Name byteArrayName
      let trace := Reader.denoteGroups (Legacy.rowsAt checked)
        (List.range checked.projection.snapshot.groupCount)
      trace.2 = .eos ∧ Stream.read ipc wire = .ok decoded ∧
      decoded.fields = fields (project selected).schema ∧
      decoded.batches.map StreamWriter.observeBatch = trace.1.map (fun group =>
        observe (AlignedColumns.ofRows ((project selected).scan (keep selected) group))) ∧
      decoded.batches.map (·.observed.rowCount) = trace.1.map (fun group =>
        (Relational.Scan.select (keep selected) group).length) ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan.convert_readback written

/-- An open refusal returns the original source cause. -/
theorem convert_open_error {cause : Legacy.Error}
    (failed : Legacy.openFile parquet input int32Name byteArrayName = .error cause) :
    convert parquet ipc input int32Name byteArrayName project keep = .error (.source cause) :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan.convert_open_error failed

/-- The original indexed source failure takes priority for every predicate
and projected schema, including a predicate that discards every row. -/
theorem convert_first_error {before after : List Nat} {index : Nat}
    {groups : List (List Int32ByteArrayGroup.Row)} {cause : Legacy.Error}
    (opened : Legacy.openFile parquet input int32Name byteArrayName = .ok checked)
    (split : List.range checked.projection.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i pairs => Legacy.readGroup checked i = .ok pairs) before groups)
    (failed : Legacy.readGroup checked index = .error cause) :
    convert parquet ipc input int32Name byteArrayName project keep = .error (.source cause) :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan.convert_first_error opened split earlier failed

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan
