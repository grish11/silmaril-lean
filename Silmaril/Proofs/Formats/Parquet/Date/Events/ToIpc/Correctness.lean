module

public import Silmaril.Formats.Parquet.Date.Events.ToIpc.Defs
import Silmaril.Formats.Arrow.DateStream.Writer.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Events.ToIpc

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Date.Events.ToIpc

private theorem mapError_ok_iff {α ε δ : Type} {result : Except ε α} {f : ε → δ} {value : α} :
    result.mapError f = .ok value ↔ result = .ok value := by
  cases result <;> simp [Except.mapError]

theorem emit_readback {limits : Arrow.ObservationLimits} {source : Source} {wire : KBytes}
    (written : emit limits source = .ok wire) :
    ∃ schema trace, ∃ column : Fin schema.width, ∃ name nullable,
      source = .ok ⟨schema, trace⟩ ∧ trace.termination = .eos ∧
      schema.width = 1 ∧ schema.kind column = (name, .date32 nullable) ∧
      Arrow.DateStream.read limits.ipc wire =
        .ok (Arrow.DateStream.Writer.observation name nullable (batchSlots trace column)) := by
  cases source with
  | error => simp [emit] at written
  | ok admitted =>
    obtain ⟨schema, trace⟩ := admitted
    cases terminal : trace.termination with
    | closed => simp [emit, terminal] at written
    | readError => simp [emit, terminal] at written
    | closeError => simp [emit, terminal] at written
    | eos =>
      by_cases one : schema.width = 1
      · let column : Fin schema.width := ⟨0, by omega⟩
        cases field : schema.kind column with
        | mk name kind =>
          cases kind with
          | date32 nullable =>
            have checked :
                (Arrow.DateStream.Writer.emit limits name nullable (batchSlots trace column)).mapError
                  Error.writer = .ok wire := by
              simpa [emit, terminal, one, column, field] using written
            refine ⟨schema, trace, column, name, nullable, rfl, terminal, one, field, ?_⟩
            exact Arrow.DateStream.Writer.emit_readback (mapError_ok_iff.mp checked)
      · simp [emit, terminal, one] at written

end Silmaril.Proofs.Formats.Parquet.Date.Events.ToIpc
