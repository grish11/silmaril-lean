module

public import Silmaril.Formats.Csv.NamedTable.Utf8.Defs
import Silmaril.Proofs.Formats.Csv.NamedTable.Utf8

/-! Exact UTF-8 CSV named insertion, rejection, and round trips. -/

public section

namespace Silmaril.Formats.Csv.NamedTable.Utf8

open Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (Packed)

variable {Name Kind : Type*} {Value : Kind → Type*}
variable {expected declared : Typed.Schema Kind}
variable {codecs : (kind : Kind) → Typed.CellCodec (Value kind)} {wire : Bytes}

/-- Success requires complete decoding and exact schema, and updates only the vacant name. -/
theorem importCsv_ok_iff [DecidableEq Name] [DecidableEq Kind]
    (db next : Packed Name Field Value) (name : Name) :
    importCsv db name expected declared codecs wire = .ok next ↔
      db name = none ∧ expected = declared ∧ ∃ rows : Typed.Table declared Value,
        Typed.Utf8.decode declared codecs wire = .ok rows ∧
        next = Function.update db name (some ⟨declared, rows⟩) :=
  Proofs.Formats.Csv.NamedTable.Utf8.importCsv_ok_iff db next name

/-- At a vacant name, a byte or typed decode error yields no updated database. -/
theorem importCsv_decode_error [DecidableEq Name] [DecidableEq Kind]
    {db : Packed Name Field Value} {name : Name} {error : Typed.Error}
    (vacant : db name = none) (decoded : Typed.Utf8.decode declared codecs wire = .error error) :
    importCsv db name expected declared codecs wire = .error (.openError error) :=
  Proofs.Formats.Csv.NamedTable.Utf8.importCsv_decode_error vacant decoded

/-- Even after complete decoding, a disagreeing ordered schema prevents insertion. -/
theorem importCsv_schema_mismatch [DecidableEq Name] [DecidableEq Kind]
    {db : Packed Name Field Value} {name : Name} {rows : Typed.Table declared Value}
    (vacant : db name = none) (decoded : Typed.Utf8.decode declared codecs wire = .ok rows)
    (different : expected ≠ declared) :
    importCsv db name expected declared codecs wire = .error .schemaMismatch :=
  Proofs.Formats.Csv.NamedTable.Utf8.importCsv_schema_mismatch vacant decoded different

/-- At an observed name, export is exactly typed UTF-8 encoding at that schema. -/
theorem exportCsv_of_observe {db : Packed Name Field Value} {name : Name}
    {table : Scan.Observation Field Value} (found : Scan.observePacked db name = some table) :
    exportCsv db name codecs =
      ((Typed.Utf8.encode table.schema codecs table.rows).map
        (fun wire => (table.schema, wire))).mapError ExportError.encodeError := by
  cases encoded : Typed.Utf8.encode table.schema codecs table.rows <;>
    simp [exportCsv, found, encoded, Except.map, Except.mapError]

/-- The exported schema is the observed schema and decoding recovers its exact ordered rows. -/
theorem decode_exportCsv (db : Packed Name Field Value) (name : Name)
    {table : Scan.Observation Field Value} (found : Scan.observePacked db name = some table)
    (law : ∀ k, (codecs k).ParsePrint)
    (written : exportCsv db name codecs = .ok (declared, wire)) :
    declared = table.schema ∧ Typed.Utf8.decode table.schema codecs wire = .ok table.rows :=
  Proofs.Formats.Csv.NamedTable.Utf8.decode_exportCsv db name found law written

/-- Export and import transfer the exact observed table into a vacant destination. -/
theorem import_exportCsv [DecidableEq Name] [DecidableEq Kind]
    (source target : Packed Name Field Value) (exportName dest : Name)
    {table : Scan.Observation Field Value} (found : Scan.observePacked source exportName = some table)
    (vacant : target dest = none) (law : ∀ k, (codecs k).ParsePrint)
    (written : exportCsv source exportName codecs = .ok (declared, wire)) :
    importCsv target dest table.schema declared codecs wire =
      .ok (Function.update target dest (some ⟨table.schema, table.rows⟩)) := by
  obtain ⟨rfl, decoded⟩ := decode_exportCsv source exportName found law written
  exact (importCsv_ok_iff target _ dest).mpr ⟨vacant, rfl, table.rows, decoded, rfl⟩

end Silmaril.Formats.Csv.NamedTable.Utf8
