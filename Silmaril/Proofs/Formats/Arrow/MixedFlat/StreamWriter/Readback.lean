module

public import Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.StreamWriter

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.MixedFlat
open Silmaril.Formats.Arrow.MixedFlat.StreamWriter

theorem emit_readback {limits : MixedFlat.Limits} {schema : Schema}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits schema batches = .ok wire) :
    ∃ decoded, Stream.read limits wire = .ok decoded ∧ decoded.fields = schema.fields ∧
      decoded.batches.map observeBatch = batches.map (BatchInput.observe schema) := by
  cases serialized : serialize limits schema batches with
  | error => simp [emit, serialized, Bind.bind, Except.bind] at written
  | ok actual =>
    cases decoded : Stream.read limits actual with
    | error =>
      simp [emit, serialized, decoded, Bind.bind, Except.bind, Except.mapError] at written
    | ok result =>
      by_cases agrees : result.fields = schema.fields ∧
          result.batches.map observeBatch = batches.map (BatchInput.observe schema)
      · have same : actual = wire := by
          simpa [emit, serialized, decoded, agrees, Bind.bind, Except.bind, Except.mapError,
            Pure.pure, Except.pure] using written
        exact ⟨result, same ▸ decoded, agrees⟩
      · simp [emit, serialized, decoded, agrees, Bind.bind, Except.bind, Except.mapError] at written

theorem emit_batch_rows {limits : MixedFlat.Limits} {schema : Schema}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits schema batches = .ok wire) :
    ∃ decoded, Stream.read limits wire = .ok decoded ∧ decoded.fields = schema.fields ∧
      decoded.batches.map (fun batch => batch.observed.rowCount) = batches.map BatchInput.rowCount := by
  obtain ⟨decoded, read, fields, observations⟩ := emit_readback written
  have rows := congrArg (List.map (Prod.fst : BatchObservation → Nat)) observations
  exact ⟨decoded, read, fields,
    by simpa [List.map_map, Function.comp_def, observeBatch, BatchInput.observe] using rows⟩

theorem emit_wire {limits : MixedFlat.Limits} {schema : Schema}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits schema batches = .ok wire) :
    wire.wf = true ∧ ∃ start decoded,
      Stream.readSchemaFrame limits.observation.ipc wire = .ok (schema.fields, start) ∧
      Stream.BatchesWire limits wire schema.fields limits.observation.ipc.batches 0 start decoded ∧
      decoded.map observeBatch = batches.map (BatchInput.observe schema) := by
  obtain ⟨decoded, read, fields, observations⟩ := emit_readback written
  obtain ⟨wf, start, header, records⟩ := (Stream.read_iff limits wire decoded).mp read
  exact ⟨wf, start, decoded.batches, fields ▸ header, fields ▸ records, observations⟩

end Silmaril.Proofs.Formats.Arrow.MixedFlat.StreamWriter
