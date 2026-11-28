module

public import Silmaril.Formats.Arrow.DateStream.ToCsv.RowObservational.Defs
import Silmaril.Proofs.Formats.Arrow.DateStream.ToCsv.RowObservational.RoundTrip

public section

namespace Silmaril.Formats.Arrow.DateStream.ToCsv.RowObservational

/-- The signed slots recover exactly the checked reader's flattened civil dates,
including null positions, under the supplied DAY descriptor. -/
theorem readRows_eq_ok_iff {ipc : Limits} {name : String} {nullable : Bool}
    {input : KBytes} {slots : Writer.Column} :
    readRows ipc name nullable input = .ok slots ↔
      ∃ source, DateStream.read ipc input = .ok source ∧ source.field = ⟨name, nullable, .day⟩ ∧
        slots.map (Option.map DateInterop.Date32.toCivil) = source.batches.flatten :=
  Proofs.Formats.Arrow.DateStream.ToCsv.RowObservational.readRows_eq_ok_iff

/-- The canonical CSV success contract checks total rows and output bytes
in addition to the checked IPC read. -/
theorem exportRows_eq_ok_iff {ipc : Limits} {csv : FromCsv.CsvLimits} {name : String}
    {nullable : Bool} {input : KBytes} {wire : Csv.Bytes} :
    exportRows ipc csv name nullable input = .ok wire ↔
      wire.length ≤ csv.maxBytes ∧
      ∃ slots, readRows ipc name nullable input = .ok slots ∧ slots.length ≤ csv.maxRows ∧
        Csv.Typed.Codecs.Date32.encode (FromCsv.schema name nullable) id (rows name nullable slots) =
          .ok wire :=
  Proofs.Formats.Arrow.DateStream.ToCsv.RowObservational.exportRows_eq_ok_iff

/-- Two successful exports under one declaration have identical canonical
bytes exactly when their ordered nullable signed rows are equal. -/
theorem exportRows_eq_iff {ipc : Limits} {csv : FromCsv.CsvLimits} {name : String}
    {nullable : Bool} {left right : KBytes} {leftWire rightWire : Csv.Bytes}
    (wroteLeft : exportRows ipc csv name nullable left = .ok leftWire)
    (wroteRight : exportRows ipc csv name nullable right = .ok rightWire) :
    leftWire = rightWire ↔ readRows ipc name nullable left = readRows ipc name nullable right :=
  Proofs.Formats.Arrow.DateStream.ToCsv.RowObservational.exportRows_eq_iff wroteLeft wroteRight

/-- Successful reimport preserves the descriptor and writes the observed rows
as one explicit batch, including the empty row list. -/
theorem reimport_readback {ipc : Limits} {reimport : ObservationLimits}
    {csv : FromCsv.CsvLimits} {name : String} {nullable : Bool} {input output : KBytes}
    {wire : Csv.Bytes} (exported : exportRows ipc csv name nullable input = .ok wire)
    (imported : FromCsv.convert reimport csv name nullable wire = .ok output) :
    ∃ slots, readRows ipc name nullable input = .ok slots ∧
      DateStream.read reimport.ipc output = .ok (Writer.observation name nullable [slots]) :=
  Proofs.Formats.Arrow.DateStream.ToCsv.RowObservational.reimport_readback exported imported

end Silmaril.Formats.Arrow.DateStream.ToCsv.RowObservational
