module

public import Silmaril.Formats.Arrow.TimestampStream.ToCsv.Defs
import Silmaril.Proofs.Formats.Arrow.TimestampStream.ToCsv.Correctness

/-! Exact completion, named insertion, and typed CSV readback. -/

public section

namespace Silmaril.Formats.Arrow.TimestampStream.ToCsv

open Silmaril.Relational Silmaril.Numeric.Timestamp
open Silmaril.Formats.Relational.NamedTable (Packed)

/-- Printing a bounded timestamp tick and reading it at the same descriptor
recovers the original value. -/
theorem codecs_parsePrint (kind : Kind) : (codecs kind).ParsePrint :=
  Proofs.Formats.Arrow.TimestampStream.ToCsv.codecs_parsePrint kind

/-- The sole slot of each output row is the corresponding input slot. -/
theorem rows_order (stream : Stream) :
    (rows stream).map (fun row => row ⟨0, by simp [schemaOf]⟩) = stream.batches.flatten := by
  change (stream.batches.flatten.map (fun slot (_ : Fin 1) => slot)).map
    (fun row : Fin 1 → Option (TimestampBatch.Value stream.binding) => row 0) = stream.batches.flatten
  rw [List.map_map]
  exact List.map_id _

variable {Name : Type*} [DecidableEq Name]
variable {db : Packed Name Csv.Field Cell} {name : Name} {ipcLimits : Arrow.Limits}
variable {csvLimits : CsvLimits} {input : KBytes}

/-- A failed IPC read at a vacant name returns its indexed cause alone. -/
theorem convert_read_error {reason : TimestampStream.Error} (vacant : db name = none)
    (failed : read ipcLimits input = .error reason) :
    convert db name ipcLimits csvLimits input = .error (.input reason) := by
  simp [convert, vacant, failed]

/-- A completed read, a representable typed export and the declared limits
produce the exact named update and wire. -/
theorem convert_of_read {stream : Stream} {wire : Csv.Bytes}
    (vacant : db name = none) (read : read ipcLimits input = .ok stream)
    (rowsFit : (rows stream).length ≤ csvLimits.maxRows)
    (encoded : Csv.Typed.Utf8.encode (schemaOf stream.binding) codecs (rows stream) = .ok wire)
    (bytesFit : wire.length ≤ csvLimits.maxBytes) :
    convert db name ipcLimits csvLimits input =
      .ok ⟨Function.update db name (some ⟨schemaOf stream.binding, rows stream⟩), schemaOf stream.binding, wire⟩ :=
  Proofs.Formats.Arrow.TimestampStream.ToCsv.convert_of_read vacant read rowsFit encoded bytesFit

/-- Success returns the original descriptor and exact named update. Decoding
with the returned declaration recovers the ordered nullable timestamp rows. -/
theorem convert_readback {result : Csv.EventStream.Result Name Cell}
    (converted : convert db name ipcLimits csvLimits input = .ok result) :
    db name = none ∧ ∃ stream : Stream,
      read ipcLimits input = .ok stream ∧
      result.schema = schemaOf stream.binding ∧
      result.db = Function.update db name (some ⟨schemaOf stream.binding, rows stream⟩) ∧
      Csv.Typed.Utf8.decode (schemaOf stream.binding) codecs result.wire = .ok (rows stream) ∧
      (rows stream).length ≤ csvLimits.maxRows ∧ result.wire.length ≤ csvLimits.maxBytes :=
  Proofs.Formats.Arrow.TimestampStream.ToCsv.convert_readback converted

end Silmaril.Formats.Arrow.TimestampStream.ToCsv
