module

public import Silmaril.Formats.Arrow.FromCsv.Stream.Defs
import Silmaril.Formats.Arrow.FromCsv.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.FromCsv.Stream

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Relational.NamedTable (Packed)
open Silmaril.Formats.Arrow.FromCsv Silmaril.Formats.Arrow.FromCsv.Stream
open Silmaril.Formats.Arrow.ToCsv (Cell schemaOf eraseRow codecs)

theorem emitAdapted_ok_iff {limits : ObservationLimits} {fields : List Field}
    {adapted : Except AdapterError Writer.BatchInput} {ipc : KBytes} :
    emitAdapted limits fields adapted = .ok ipc ↔
      ∃ input, adapted = .ok input ∧ StreamWriter.emit limits fields [input] = .ok ipc := by
  cases adapted with
  | error error => simp [emitAdapted]
  | ok input =>
    cases written : StreamWriter.emit limits fields [input] <;>
      simp [emitAdapted, Except.mapError, written]

theorem emitCsv_preserves {limits : ObservationLimits} {fields : List Field} {wire : Csv.Bytes}
    {ipc : KBytes} (written : emitCsv limits fields wire = .ok ipc) :
    ∃ (rows : Scan.Table (schemaOf fields) Cell) (input : Writer.BatchInput),
      Csv.Typed.decode (schemaOf fields) codecs wire = .ok rows ∧
      input.fields = fields ∧ input.rowCount = rows.length ∧ input.observe = rows.map (eraseRow fields) ∧
      StreamWriter.emit limits fields [input] = .ok ipc := by
  obtain ⟨input, adapted, emitted⟩ := emitAdapted_ok_iff.mp written
  obtain ⟨rows, decoded, schema, count, observe⟩ := ofCsv_preserves adapted
  exact ⟨rows, input, decoded, schema, count, observe, emitted⟩

theorem emitCsvUtf8_preserves {limits : ObservationLimits} {fields : List Field} {wire : Csv.Bytes}
    {ipc : KBytes} (written : emitCsvUtf8 limits fields wire = .ok ipc) :
    ∃ (rows : Scan.Table (schemaOf fields) Cell) (input : Writer.BatchInput),
      Csv.Typed.Utf8.decode (schemaOf fields) utf8Codecs wire = .ok rows ∧
      input.fields = fields ∧ input.rowCount = rows.length ∧ input.observe = rows.map (eraseRow fields) ∧
      StreamWriter.emit limits fields [input] = .ok ipc := by
  obtain ⟨input, adapted, emitted⟩ := emitAdapted_ok_iff.mp written
  cases decoded : Csv.Typed.Utf8.decode (schemaOf fields) utf8Codecs wire with
  | error error => simp [ofCsvUtf8, decoded, Except.mapError, Bind.bind, Except.bind] at adapted
  | ok rows =>
    have checked : ofRows fields rows = .ok input := by
      simpa [ofCsvUtf8, decoded, Except.mapError, Bind.bind, Except.bind] using adapted
    obtain ⟨schema, count, observe⟩ := ofRows_preserves checked
    exact ⟨rows, input, rfl, schema, count, observe, emitted⟩

theorem emitNamed_preserves {Name : Type} {limits : ObservationLimits} {db : Packed Name Csv.Field Cell}
    {name : Name} {fields : List Field} {ipc : KBytes} (written : emitNamed limits db name fields = .ok ipc) :
    ∃ (rows : Scan.Table (schemaOf fields) Cell) (input : Writer.BatchInput),
      Scan.observePacked db name = some ⟨schemaOf fields, rows⟩ ∧
      input.fields = fields ∧ input.rowCount = rows.length ∧ input.observe = rows.map (eraseRow fields) ∧
      StreamWriter.emit limits fields [input] = .ok ipc := by
  obtain ⟨input, adapted, emitted⟩ := emitAdapted_ok_iff.mp written
  obtain ⟨rows, found, schema, count, observe⟩ := ofNamed_preserves adapted
  exact ⟨rows, input, found, schema, count, observe, emitted⟩

end Silmaril.Proofs.Formats.Arrow.FromCsv.Stream
