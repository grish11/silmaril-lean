module

public import Silmaril.Formats.Csv.NamedTable.Utf8.Defs
import Silmaril.Formats.Csv.Typed.Utf8.Thms
import Silmaril.Formats.Relational.NamedTable.Thms
import Silmaril.Proofs.Formats.Csv.NamedTable

public section

namespace Silmaril.Proofs.Formats.Csv.NamedTable.Utf8

open Silmaril.Relational
open Silmaril.Formats.Csv
open Silmaril.Formats.Csv.NamedTable.Utf8 (importCsv exportCsv)
open Silmaril.Formats.Csv.NamedTable.Internal (importDecoded)
open Silmaril.Formats.Relational.NamedTable (Packed importCollected)

variable {Name Kind : Type*} {Value : Kind → Type*}
variable {expected declared : Typed.Schema Kind}
variable {codecs : (kind : Kind) → Typed.CellCodec (Value kind)} {wire : Bytes}

theorem importCsv_ok_iff [DecidableEq Name] [DecidableEq Kind]
    (db next : Packed Name Field Value) (name : Name) :
    importCsv db name expected declared codecs wire = .ok next ↔
      db name = none ∧ expected = declared ∧ ∃ rows : Typed.Table declared Value,
        Typed.Utf8.decode declared codecs wire = .ok rows ∧
        next = Function.update db name (some ⟨declared, rows⟩) :=
  importDecoded_ok_iff db next name (Typed.Utf8.decode declared codecs wire)

theorem importCsv_decode_error [DecidableEq Name] [DecidableEq Kind]
    {db : Packed Name Field Value} {name : Name} {error : Typed.Error}
    (vacant : db name = none) (decoded : Typed.Utf8.decode declared codecs wire = .error error) :
    importCsv db name expected declared codecs wire = .error (.openError error) := by
  simp [importCsv, importDecoded, decoded, importCollected, vacant, Except.map]

theorem importCsv_schema_mismatch [DecidableEq Name] [DecidableEq Kind]
    {db : Packed Name Field Value} {name : Name} {rows : Typed.Table declared Value}
    (vacant : db name = none) (decoded : Typed.Utf8.decode declared codecs wire = .ok rows)
    (different : expected ≠ declared) :
    importCsv db name expected declared codecs wire = .error .schemaMismatch := by
  simp [importCsv, importDecoded, decoded, importCollected, vacant, Except.map, different]

theorem decode_exportCsv (db : Packed Name Field Value) (name : Name)
    {table : Scan.Observation Field Value} (found : Scan.observePacked db name = some table)
    (law : ∀ k, (codecs k).ParsePrint)
    (written : exportCsv db name codecs = .ok (declared, wire)) :
    declared = table.schema ∧ Typed.Utf8.decode table.schema codecs wire = .ok table.rows := by
  obtain ⟨same, encoded⟩ := exportWith_observe found written
  exact ⟨same, Typed.Utf8.decode_encode law encoded⟩

end Silmaril.Proofs.Formats.Csv.NamedTable.Utf8
