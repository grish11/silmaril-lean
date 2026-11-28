module

public import Silmaril.Formats.Arrow.DateStream.FromCsv.Defs
public import Silmaril.Formats.Arrow.DateStream.Writer.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.DateStream.FromCsv

open Silmaril.Formats
open Arrow
open DateStream.FromCsv

theorem convert_eq_ok_iff {ipc : ObservationLimits} {csv : CsvLimits} {name : String}
    {nullable : Bool} {input : Csv.Bytes} {wire : KBytes} :
    convert ipc csv name nullable input = .ok wire ↔
      input.length ≤ csv.maxBytes ∧
      ∃ rows, Csv.Typed.Codecs.Date32.decode (schema name nullable) id input = .ok rows ∧
        rows.length ≤ csv.maxRows ∧
        DateStream.Writer.emit ipc name nullable [slots rows] = .ok wire := by
  unfold convert
  by_cases bytes : input.length ≤ csv.maxBytes
  · simp only [bytes, not_lt.mpr bytes, ite_false, true_and]
    cases Csv.Typed.Codecs.Date32.decode (schema name nullable) id input with
    | error reason =>
      simp [Except.mapError, Bind.bind, Except.bind]
    | ok rows =>
      by_cases count : rows.length ≤ csv.maxRows
      · cases written : DateStream.Writer.emit ipc name nullable [slots rows] <;>
          simp [Except.mapError, Bind.bind, Except.bind, not_lt.mpr count, count, written]
      · simp [Except.mapError, Bind.bind, Except.bind, Nat.lt_of_not_ge count, count,
          MonadExcept.throw]
  · simp [Nat.lt_of_not_ge bytes, bytes, MonadExcept.throw, Bind.bind, Except.bind]

theorem convert_readback {ipc : ObservationLimits} {csv : CsvLimits} {name : String}
    {nullable : Bool} {input : Csv.Bytes} {wire : KBytes}
    (converted : convert ipc csv name nullable input = .ok wire) :
    ∃ rows stream, Csv.Typed.Codecs.Date32.decode (schema name nullable) id input = .ok rows ∧
      DateStream.read ipc.ipc wire = .ok stream ∧
      stream = DateStream.Writer.observation name nullable [slots rows] ∧
      stream.batches.map (List.map (fun slot => slot.bind DateInterop.Date32.ofCivil?)) =
        [slots rows] := by
  obtain ⟨_, rows, parsed, _, written⟩ := convert_eq_ok_iff.mp converted
  exact ⟨rows, _, parsed, DateStream.Writer.emit_readback written, rfl,
    DateStream.Writer.observation_words name nullable [slots rows]⟩

end Silmaril.Proofs.Formats.Arrow.DateStream.FromCsv
