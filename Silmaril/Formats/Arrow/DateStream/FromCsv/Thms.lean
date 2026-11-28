module

public import Silmaril.Formats.Arrow.DateStream.FromCsv.Defs
import Silmaril.Proofs.Formats.Arrow.DateStream.FromCsv.Readback

public section

namespace Silmaril.Formats.Arrow.DateStream.FromCsv

/-- Success requires both CSV bounds, the existing typed decode, and emission
of exactly one batch under the supplied IPC limits. -/
theorem convert_eq_ok_iff {ipc : ObservationLimits} {csv : CsvLimits} {name : String}
    {nullable : Bool} {input : Csv.Bytes} {wire : KBytes} :
    convert ipc csv name nullable input = .ok wire ↔
      input.length ≤ csv.maxBytes ∧
      ∃ rows, Csv.Typed.Codecs.Date32.decode (schema name nullable) id input = .ok rows ∧
        rows.length ≤ csv.maxRows ∧ Writer.emit ipc name nullable [slots rows] = .ok wire :=
  Proofs.Formats.Arrow.DateStream.FromCsv.convert_eq_ok_iff

/-- The checked DATE reader recovers the supplied name and nullability, the
DAY unit, and exactly one ordered batch of the original nullable signed words. -/
theorem convert_readback {ipc : ObservationLimits} {csv : CsvLimits} {name : String}
    {nullable : Bool} {input : Csv.Bytes} {wire : KBytes}
    (converted : convert ipc csv name nullable input = .ok wire) :
    ∃ rows stream, Csv.Typed.Codecs.Date32.decode (schema name nullable) id input = .ok rows ∧
      DateStream.read ipc.ipc wire = .ok stream ∧
      stream = DateStream.Writer.observation name nullable [slots rows] ∧
      stream.batches.map (List.map (fun slot => slot.bind DateInterop.Date32.ofCivil?)) =
        [slots rows] :=
  Proofs.Formats.Arrow.DateStream.FromCsv.convert_readback converted

/-- Once the byte cap passes, typed CSV failures are returned before the row
cap or IPC writer is checked. -/
theorem convert_csv_error {ipc : ObservationLimits} {csv : CsvLimits} {name : String}
    {nullable : Bool} {input : Csv.Bytes} {cause : Csv.Typed.Codecs.Date32.Error}
    (bytes : input.length ≤ csv.maxBytes)
    (bad : Csv.Typed.Codecs.Date32.decode (schema name nullable) id input = .error cause) :
    convert ipc csv name nullable input = .error (.csv cause) := by
  simp [convert, not_lt.mpr bytes, bad, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Arrow.DateStream.FromCsv
