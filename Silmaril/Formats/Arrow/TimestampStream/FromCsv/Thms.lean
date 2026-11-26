module

public import Silmaril.Formats.Arrow.TimestampStream.FromCsv.Defs
import Silmaril.Proofs.Formats.Arrow.TimestampStream.FromCsv.Correctness

/-! Exact frame admission and certified TIMESTAMP CSV to IPC readback. -/

public section

namespace Silmaril.Formats.Arrow.TimestampStream.FromCsv

open Silmaril.Relational
open ToCsv (Cell CsvLimits Kind codecs schemaOf)
open Silmaril.Formats.Relational.NamedTable (Packed)

/-- The supplied frame is well-formed, consumed exactly, and has the declared descriptor. -/
theorem checkSchema_sound {ipc : Arrow.Limits} {declared : Csv.Typed.Schema Kind} {frame : KBytes}
    {binding : TimestampBatch.Binding} (checked : checkSchema ipc declared frame = .ok binding) :
    frame.wf = true ∧ TimestampStream.readSchema ipc frame = .ok (binding, frame.len) ∧
      schemaOf binding = declared :=
  Proofs.Formats.Arrow.TimestampStream.FromCsv.checkSchema_sound checked

/-- An emitted stream contains the supplied Schema frame, one emitted record and EOS.
The checked reader recovers the same descriptor and ordered signed nullable slots. -/
theorem emit_readback {ipc : Arrow.Limits} {binding : TimestampBatch.Binding} {frame wire : KBytes}
    {slots : TimestampBatch.Column binding} (emitted : emit ipc binding frame slots = .ok wire) :
    (∃ record, emitRecord ipc binding slots = .ok record ∧ wire = frame ++ record ++ StreamWriter.eos) ∧
    ∃ stream : TimestampStream.Stream,
      TimestampStream.read ipc wire = .ok stream ∧ schemaOf stream.binding = schemaOf binding ∧
      stream.batches.map tickCounts = [tickCounts slots] :=
  Proofs.Formats.Arrow.TimestampStream.FromCsv.emit_readback emitted

variable {Name : Type*} [DecidableEq Name]
variable {db : Packed Name Csv.Field Cell} {name : Name} {ipc : Arrow.Limits} {csv : CsvLimits}
variable {declared : Csv.Typed.Schema Kind} {frame : KBytes} {wire : Csv.Bytes}

/-- Success identifies the exact named insertion and the reader observation of
the emitted IPC under the original declared schema. -/
theorem convert_readback {result : Result Name}
    (converted : convert db name ipc csv declared frame wire = .ok result) :
    db name = none ∧ ∃ (binding : TimestampBatch.Binding)
      (rows : Csv.Typed.Table (schemaOf binding) Cell) (stream : TimestampStream.Stream),
      frame.wf = true ∧ TimestampStream.readSchema ipc frame = .ok (binding, frame.len) ∧
      schemaOf binding = declared ∧ Csv.Typed.Utf8.decode (schemaOf binding) codecs wire = .ok rows ∧
      wire.length ≤ csv.maxBytes ∧ rows.length ≤ csv.maxRows ∧
      result.db = Function.update db name (some ⟨schemaOf binding, rows⟩) ∧
      TimestampStream.read ipc result.wire = .ok stream ∧ schemaOf stream.binding = declared ∧
      stream.batches.map tickCounts = [tickCounts (slotsOf binding rows)] :=
  Proofs.Formats.Arrow.TimestampStream.FromCsv.convert_readback converted

end Silmaril.Formats.Arrow.TimestampStream.FromCsv
