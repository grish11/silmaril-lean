module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Thms
import Silmaril.Formats.Arrow.Writer.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow.MixedFlat
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan

variable {parquet : Legacy.Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes}
variable {int32Name byteArrayName : String} {project : Projection} {keep : Predicate} {wire : KBytes}
variable {checked : Legacy.Checked parquet int32Name byteArrayName}

private theorem orderedField (label : String × Legacy.Kind)
    (values : List (Option (Legacy.Value label.2))) :
    ((Column.ofValues label.2 values).toOrdered (field label)).field = field label := by
  rcases label with ⟨name, kind⟩
  cases kind <;> rfl

private theorem orderedCells (label : Arrow.MixedFlat.Field)
    (column : Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan.Column) :
    (column.toOrdered label).observe = column.observe := by
  cases column with
  | int32 => rfl
  | binary values =>
    change Writer.ColumnObservation.binaryView ((binaryValues values).map (Option.map KBytes.toList)) =
      Writer.ColumnObservation.binaryView (values.map (Option.map Bytes.toList))
    congr 1
    rw [binaryValues, List.map_map]
    apply List.map_congr_left
    intro value _
    cases value <;> simp [Arrow.Writer.emitBytes_bytes]

theorem orderedBatch_exact {selected : Schema} (batch : Batch selected) :
    (orderedBatch batch).fields = fields selected ∧ (orderedBatch batch).observe = observe batch := by
  constructor
  · simp only [orderedBatch, OrderedWriter.BatchInput.fields, fields, List.map_ofFn]
    exact congrArg List.ofFn (funext fun i => orderedField (selected.kind i) (batch.values i))
  · simp only [orderedBatch, OrderedWriter.BatchInput.observe, observe, List.map_ofFn]
    congr 3
    funext i
    exact Prod.ext (orderedField (selected.kind i) (batch.values i)) (orderedCells _ _)

theorem emit_readback {selected : Schema} {batches : List (Batch selected)}
    (written : emit ipc selected batches = .ok wire) :
    ∃ decoded, Stream.read ipc wire = .ok decoded ∧ decoded.fields = fields selected ∧
      decoded.batches.map StreamWriter.observeBatch = batches.map observe := by
  unfold emit at written
  cases serialized : serialize ipc selected batches with
  | error cause => simp [serialized, Bind.bind, Except.bind] at written
  | ok bytes =>
    cases read : Stream.read ipc bytes with
    | error cause => simp [serialized, read, Except.mapError, Bind.bind, Except.bind] at written
    | ok decoded =>
      simp only [serialized, read, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at written
      split at written
      · next agrees =>
        cases written
        exact ⟨decoded, read, agrees.1, agrees.2⟩
      · contradiction

theorem convert_open_error {cause : Legacy.Error}
    (failed : Legacy.openFile parquet input int32Name byteArrayName = .error cause) :
    convert parquet ipc input int32Name byteArrayName project keep = .error (.source cause) := by
  simp [convert, Legacy.readAll, Legacy.openSource, failed, Parquet.Reader.readAll,
    Arrow.Events.EventStream.scan, Except.map, Except.mapError, Bind.bind, Except.bind]

theorem convert_readback
    (written : convert parquet ipc input int32Name byteArrayName project keep = .ok wire) :
    ∃ (checked : Legacy.Checked parquet int32Name byteArrayName) (decoded : Stream.Observed),
      Legacy.openFile parquet input int32Name byteArrayName = .ok checked ∧
      let selected := Legacy.schema int32Name byteArrayName
      let trace := Parquet.Reader.denoteGroups (Legacy.rowsAt checked)
        (List.range checked.projection.snapshot.groupCount)
      trace.2 = .eos ∧ Stream.read ipc wire = .ok decoded ∧
      decoded.fields = fields (project selected).schema ∧
      decoded.batches.map StreamWriter.observeBatch = trace.1.map (fun group =>
        observe (AlignedColumns.ofRows ((project selected).scan (keep selected) group))) ∧
      decoded.batches.map (·.observed.rowCount) = trace.1.map (fun group =>
        (Relational.Scan.select (keep selected) group).length) ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches := by
  cases opened : Legacy.openFile parquet input int32Name byteArrayName with
  | error cause => rw [convert_open_error opened] at written; contradiction
  | ok checked =>
    let selected := Legacy.schema int32Name byteArrayName
    let trace := Parquet.Reader.denoteGroups (Legacy.rowsAt checked)
      (List.range checked.projection.snapshot.groupCount)
    have scanned := Legacy.scan_readAll_order project keep opened
    simp only [convert, scanned, Except.mapError, Bind.bind, Except.bind] at written
    change (match trace.2 with
      | .eos => emit ipc (project selected).schema (trace.1.map fun group =>
          AlignedColumns.ofRows ((project selected).scan (keep selected) group))
      | .readError cause | .closeError cause => Except.error (Error.source cause)
      | .closed => Except.error Error.closed) = .ok wire at written
    cases terminal : trace.2 <;> rw [terminal] at written <;> try contradiction
    obtain ⟨decoded, read, schema, batches⟩ := emit_readback written
    have counts := congrArg (List.map (fun batch : StreamWriter.BatchObservation => batch.1)) batches
    refine ⟨checked, decoded, rfl, terminal, read, schema, ?_, ?_, (Stream.read_iff ipc wire decoded).mp read⟩
    · simpa only [List.map_map, Function.comp_def] using batches
    · simpa only [List.map_map, Function.comp_def, StreamWriter.observeBatch, observe,
        AlignedColumns.ofRows, Relational.Scan.Projection.scan, Relational.Scan.Projection.project,
        List.length_map] using counts

theorem convert_first_error {before after : List Nat} {index : Nat}
    {groups : List (List Parquet.Int32ByteArrayGroup.Row)} {cause : Legacy.Error}
    (opened : Legacy.openFile parquet input int32Name byteArrayName = .ok checked)
    (split : List.range checked.projection.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i pairs => Legacy.readGroup checked i = .ok pairs) before groups)
    (failed : Legacy.readGroup checked index = .error cause) :
    convert parquet ipc input int32Name byteArrayName project keep = .error (.source cause) := by
  simp [convert, Legacy.scan_readAll_first_error project keep opened split earlier failed,
    Except.mapError, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan
