module

public import Silmaril.Formats.Arrow.DateStream.ToCsv.Defs
import Silmaril.Proofs.Formats.Arrow.DateStream.ToCsv.RoundTrip

public section

namespace Silmaril.Formats.Arrow.DateStream.ToCsv

namespace Internal

theorem recover_eq_some_iff (dates : DateValues.Column) (slots : Writer.Column) :
    recover dates = some slots ↔ slots.map (Option.map DateInterop.Date32.toCivil) = dates :=
  Proofs.Formats.Arrow.DateStream.ToCsv.recover_eq_some_iff dates slots

theorem encodeColumn_eq_ok_iff {csv : FromCsv.CsvLimits} {name : String} {nullable : Bool}
    {slots : Writer.Column} {output : Csv.Bytes} :
    encodeColumn csv name nullable slots = .ok output ↔
      output.length ≤ csv.maxBytes ∧ slots.length ≤ csv.maxRows ∧
      Csv.Typed.Codecs.Date32.encode (FromCsv.schema name nullable) id
        (rows name nullable slots) = .ok output :=
  Proofs.Formats.Arrow.DateStream.ToCsv.encodeColumn_eq_ok_iff

end Internal

/-- Readback requires the exact name, nullability and DAY unit, and one
explicit batch with the original ordered signed nullable slots. -/
theorem readColumn_eq_ok_iff {ipc : Limits} {name : String} {nullable : Bool}
    {input : KBytes} {slots : Writer.Column} :
    readColumn ipc name nullable input = .ok slots ↔
      DateStream.read ipc input = .ok (Writer.observation name nullable [slots]) :=
  Proofs.Formats.Arrow.DateStream.ToCsv.readColumn_eq_ok_iff

/-- Export succeeds exactly when the admitted IPC observation encodes to the
canonical typed CSV and both CSV output bounds pass. -/
theorem convert_eq_ok_iff {ipc : Limits} {csv : FromCsv.CsvLimits} {name : String}
    {nullable : Bool} {input : KBytes} {output : Csv.Bytes} :
    convert ipc csv name nullable input = .ok output ↔
      output.length ≤ csv.maxBytes ∧
      ∃ slots, DateStream.read ipc input = .ok (Writer.observation name nullable [slots]) ∧
        slots.length ≤ csv.maxRows ∧
        Csv.Typed.Codecs.Date32.encode (FromCsv.schema name nullable) id
          (rows name nullable slots) = .ok output :=
  Proofs.Formats.Arrow.DateStream.ToCsv.convert_eq_ok_iff

/-- The canonical export preserves exact lexical rows after CSV decoding.
Canonical quoting and CRLF can increase the byte count. Re-export succeeds
with the same limits exactly when the canonical bytes fit. -/
theorem csv_roundtrip {ipc : ObservationLimits} {csv : FromCsv.CsvLimits} {name : String}
    {nullable : Bool} {input : Csv.Bytes} {wire : KBytes}
    (written : FromCsv.convert ipc csv name nullable input = .ok wire) :
    ∃ table canonical,
      Csv.Typed.Codecs.Date32.decode (FromCsv.schema name nullable) id input = .ok table ∧
      Csv.Typed.Codecs.Date32.encode (FromCsv.schema name nullable) id table = .ok canonical ∧
      Csv.Utf8.decode canonical = Csv.Utf8.decode input ∧
      (convert ipc.ipc csv name nullable wire = .ok canonical ↔ canonical.length ≤ csv.maxBytes) :=
  Proofs.Formats.Arrow.DateStream.ToCsv.csv_roundtrip written

/-- Canonical CSV input is recovered byte for byte after a successful import. -/
theorem canonical_csv_roundtrip {ipc : ObservationLimits} {csv : FromCsv.CsvLimits}
    {name : String} {nullable : Bool} {input : Csv.Bytes} {wire : KBytes}
    {table : Csv.Typed.Table (FromCsv.schema name nullable) Csv.Typed.Codecs.Date32.Cell}
    (canonical : Csv.Typed.Codecs.Date32.encode (FromCsv.schema name nullable) id table = .ok input)
    (written : FromCsv.convert ipc csv name nullable input = .ok wire) :
    convert ipc.ipc csv name nullable wire = .ok input :=
  Proofs.Formats.Arrow.DateStream.ToCsv.canonical_csv_roundtrip canonical written

/-- With the same declaration and limits, two successful legs preserve the
checked single-batch IPC observation. This includes one explicit empty batch. -/
theorem ipc_roundtrip {ipc : ObservationLimits} {csv : FromCsv.CsvLimits} {name : String}
    {nullable : Bool} {input output : KBytes} {wire : Csv.Bytes}
    (exported : convert ipc.ipc csv name nullable input = .ok wire)
    (imported : FromCsv.convert ipc csv name nullable wire = .ok output) :
    ∃ slots, DateStream.read ipc.ipc input = .ok (Writer.observation name nullable [slots]) ∧
      DateStream.read ipc.ipc output = .ok (Writer.observation name nullable [slots]) :=
  Proofs.Formats.Arrow.DateStream.ToCsv.ipc_roundtrip exported imported

end Silmaril.Formats.Arrow.DateStream.ToCsv
