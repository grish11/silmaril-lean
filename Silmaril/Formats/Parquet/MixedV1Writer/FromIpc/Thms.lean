module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Defs
import Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Correctness

public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.FromIpc

open Silmaril.Formats.Relational.NamedTable

/-- The plan preserves exact labels, nullability and ordered pairs for every source batch. -/
theorem prepare_exact {source : MixedIpc.Prepared} {plan : Multi.Input}
    (checked : prepare source = .ok plan) :
    source.descriptor.viewFirst = false ∧ source.batches ≠ [] ∧
    plan.intField = field source.descriptor.integer ∧ plan.byteField = field source.descriptor.binary ∧
    plan.groups.map Multi.Group.rows = source.batches.map (List.map toRow) :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.prepare_exact checked

/-- Success consists of full checked IPC admission, compatible planning, and checked emission. -/
theorem convert_ok_iff {source : MixedIpc.Limits} {sink : Multi.Limits} {input : KBytes}
    {output : Multi.Encoded} :
    convert source sink input = .ok output ↔
      ∃ observed plan, MixedIpc.read source input = .ok observed ∧
        prepare observed = .ok plan ∧ Multi.emit sink plan = .ok output :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.convert_ok_iff

/-- Each checked IPC RecordBatch becomes the original Parquet group ordinal, with the exact raw slots.
A zero-row batch yields a zero-row group. -/
theorem convert_indexed {source : MixedIpc.Limits} {sink : Multi.Limits} {input : KBytes}
    {output : Multi.Encoded} (written : convert source sink input = .ok output) :
    ∃ (observed : MixedIpc.Prepared) (opened : Int32ByteArrayGroup.Checked
        (field observed.descriptor.integer) (field observed.descriptor.binary)),
      MixedIpc.read source input = .ok observed ∧
      observed.descriptor.viewFirst = false ∧
      Int32ByteArrayGroup.openFile sink.writer.readback output.bytes
        (field observed.descriptor.integer) (field observed.descriptor.binary) = .ok opened ∧
      opened.snapshot.groupCount = observed.batches.length ∧
      ∀ i : Fin observed.batches.length,
        opened.readGroup sink.writer.readback i.val = .ok ((observed.batches.get i).map toRow) ∧
        Int32ByteArrayGroup.GroupWire opened sink.writer.readback i.val ((observed.batches.get i).map toRow) :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.convert_indexed written

/-- An indexed or admission failure from the source stays intact. -/
theorem convert_source_error {source : MixedIpc.Limits} {sink : Multi.Limits} {input : KBytes}
    {cause : MixedIpc.Error} (failed : MixedIpc.read source input = .error cause) :
    convert source sink input = .error (.source cause) := by
  simp [convert, failed, Except.mapError, Bind.bind, Except.bind]

/-- Schema-only streams have no group to emit under the nonempty plan policy. -/
theorem convert_schema_only {source : MixedIpc.Limits} {sink : Multi.Limits} {input : KBytes}
    {observed : MixedIpc.Prepared} (read : MixedIpc.read source input = .ok observed)
    (ordered : observed.descriptor.viewFirst = false) (empty : observed.batches = []) :
    convert source sink input = .error (.plan .noBatches) := by
  simp [convert, read, prepare, ordered, empty, Except.mapError, Bind.bind, Except.bind]

/-- After checked admission and compatible planning, a sink refusal returns its original cause. -/
theorem convert_sink_error {source : MixedIpc.Limits} {sink : Multi.Limits} {input : KBytes}
    {observed : MixedIpc.Prepared} {plan : Multi.Input} {cause : Multi.Error}
    (read : MixedIpc.read source input = .ok observed) (planned : prepare observed = .ok plan)
    (failed : Multi.emit sink plan = .error cause) :
    convert source sink input = .error (.sink cause) := by
  simp [convert, read, planned, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.MixedV1Writer.FromIpc
