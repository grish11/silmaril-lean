module

public import Silmaril.Formats.Arrow.FromCsv.Stream.Defs
import Silmaril.Proofs.Formats.Arrow.FromCsv.Stream

/-! Component laws for the typed source and the successful stream writer call. -/

public section

namespace Silmaril.Formats.Arrow.FromCsv.Stream

open Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (Packed)
open ToCsv (Cell schemaOf eraseRow codecs)

/-- Success passes the original field declaration and exactly one batch to the writer. -/
theorem emitAdapted_ok_iff {limits : ObservationLimits} {fields : List Field}
    {adapted : Except AdapterError Writer.BatchInput} {ipc : KBytes} :
    emitAdapted limits fields adapted = .ok ipc ↔
      ∃ input, adapted = .ok input ∧ StreamWriter.emit limits fields [input] = .ok ipc :=
  Proofs.Formats.Arrow.FromCsv.Stream.emitAdapted_ok_iff

theorem emitAdapted_adapterError (limits : ObservationLimits) (fields : List Field)
    (error : AdapterError) : emitAdapted limits fields (.error error) = .error (.adapter error) := rfl

theorem emitAdapted_writerError {limits : ObservationLimits} {fields : List Field}
    {input : Writer.BatchInput} {error : Error}
    (failed : StreamWriter.emit limits fields [input] = .error error) :
    emitAdapted limits fields (.ok input) = .error (.writer error) := by
  simp [emitAdapted, failed, Except.mapError]

theorem emitCsv_preserves {limits : ObservationLimits} {fields : List Field} {wire : Csv.Bytes}
    {ipc : KBytes} (written : emitCsv limits fields wire = .ok ipc) :
    ∃ (rows : Scan.Table (schemaOf fields) Cell) (input : Writer.BatchInput),
      Csv.Typed.decode (schemaOf fields) codecs wire = .ok rows ∧
      input.fields = fields ∧ input.rowCount = rows.length ∧ input.observe = rows.map (eraseRow fields) ∧
      StreamWriter.emit limits fields [input] = .ok ipc :=
  Proofs.Formats.Arrow.FromCsv.Stream.emitCsv_preserves written

theorem emitCsvUtf8_preserves {limits : ObservationLimits} {fields : List Field} {wire : Csv.Bytes}
    {ipc : KBytes} (written : emitCsvUtf8 limits fields wire = .ok ipc) :
    ∃ (rows : Scan.Table (schemaOf fields) Cell) (input : Writer.BatchInput),
      Csv.Typed.Utf8.decode (schemaOf fields) utf8Codecs wire = .ok rows ∧
      input.fields = fields ∧ input.rowCount = rows.length ∧ input.observe = rows.map (eraseRow fields) ∧
      StreamWriter.emit limits fields [input] = .ok ipc :=
  Proofs.Formats.Arrow.FromCsv.Stream.emitCsvUtf8_preserves written

theorem emitNamed_preserves {Name : Type} {limits : ObservationLimits} {db : Packed Name Csv.Field Cell}
    {name : Name} {fields : List Field} {ipc : KBytes} (written : emitNamed limits db name fields = .ok ipc) :
    ∃ (rows : Scan.Table (schemaOf fields) Cell) (input : Writer.BatchInput),
      Scan.observePacked db name = some ⟨schemaOf fields, rows⟩ ∧
      input.fields = fields ∧ input.rowCount = rows.length ∧ input.observe = rows.map (eraseRow fields) ∧
      StreamWriter.emit limits fields [input] = .ok ipc :=
  Proofs.Formats.Arrow.FromCsv.Stream.emitNamed_preserves written

end Silmaril.Formats.Arrow.FromCsv.Stream
