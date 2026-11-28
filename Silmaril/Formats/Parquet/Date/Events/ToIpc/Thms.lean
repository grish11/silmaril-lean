module

public import Silmaril.Formats.Parquet.Date.Events.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.Date.Events.ToIpc.Correctness

public section

namespace Silmaril.Formats.Parquet.Date.Events.ToIpc

/-- Successful emission exposes exactly the completed typed trace in native IPC. -/
theorem emit_readback {limits : Arrow.ObservationLimits} {source : Source} {wire : KBytes}
    (written : emit limits source = .ok wire) :
    ∃ schema trace, ∃ column : Fin schema.width, ∃ name nullable,
      source = .ok ⟨schema, trace⟩ ∧ trace.termination = .eos ∧
      schema.width = 1 ∧ schema.kind column = (name, .date32 nullable) ∧
      Arrow.DateStream.read limits.ipc wire =
        .ok (Arrow.DateStream.Writer.observation name nullable (batchSlots trace column)) :=
  Proofs.Formats.Parquet.Date.Events.ToIpc.emit_readback written

/-- A returned stream has the source's exact logical field and nullable
batches in row-group order through EOS. -/
theorem convert_readback {inputLimits : Date.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {wire : KBytes} (written : convert inputLimits outputLimits input = .ok wire) :
    ∃ schema trace, ∃ column : Fin schema.width, ∃ name nullable,
      Date.Events.readAll inputLimits input = .ok ⟨schema, trace⟩ ∧ trace.termination = .eos ∧
      schema.width = 1 ∧ schema.kind column = (name, .date32 nullable) ∧
      Arrow.DateStream.read outputLimits.ipc wire =
        .ok (Arrow.DateStream.Writer.observation name nullable (batchSlots trace column)) :=
  Proofs.Formats.Parquet.Date.Events.ToIpc.emit_readback written

/-- Opening failures preserve their original cause and yield no output. -/
theorem convert_openError {inputLimits : Date.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {cause : Date.Events.Error}
    (failed : Date.Events.readAll inputLimits input = .error cause) :
    convert inputLimits outputLimits input = .error (.source cause) := by
  simp [convert, emit, failed]

/-- A late read failure keeps the original indexed cause even when complete
batches precede it. The result contains no completed IPC stream. -/
theorem convert_readError {inputLimits : Date.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {cause : Date.Events.Error} {admitted : Σ schema,
      Arrow.Events.Trace schema Cell Date.Events.Error}
    (opened : Date.Events.readAll inputLimits input = .ok admitted)
    (failed : admitted.2.termination = .readError cause) :
    convert inputLimits outputLimits input = .error (.source cause) := by
  obtain ⟨schema, trace⟩ := admitted
  change trace.termination = .readError cause at failed
  simp [convert, emit, opened, failed]

end Silmaril.Formats.Parquet.Date.Events.ToIpc
