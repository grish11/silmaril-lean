module

public import Silmaril.Formats.Csv.NamedTable.Defs
import Silmaril.Proofs.Formats.Csv.NamedTable
import Silmaril.Formats.Relational.NamedTable.Thms
import Silmaril.Formats.Parquet.Reader.Thms

/-! Exact named CSV observation and cross-format round trips. -/

public section

namespace Silmaril.Formats.Csv.NamedTable

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Relational.NamedTable (Packed importArrow importArrow_observe importParquet)

variable {Name Kind Group Error : Type*} {Value : Kind → Type*}
variable {expected declared : Typed.Schema Kind}
variable {codecs : (kind : Kind) → Typed.CellCodec (Value kind)} {wire : Bytes}

/-- Translating a decoded CSV table to events preserves the whole observation. -/
theorem collect_eventsOfBytes (declared : Typed.Schema Kind)
    (codecs : (kind : Kind) → Typed.CellCodec (Value kind)) (wire : Bytes) :
    (eventsOfBytes declared codecs wire).collect =
      (Typed.decode declared codecs wire).map (fun rows => ⟨⟨declared, rows⟩, .eos⟩) :=
  Proofs.Formats.Csv.NamedTable.collect_eventsOfBytes declared codecs wire

/-- The entire CSV must decode under the declared schema. Only the vacant
destination can be updated, and its expected schema must match exactly. -/
theorem importCsv_ok_iff [DecidableEq Name] [DecidableEq Kind]
    (db next : Packed Name Field Value) (name : Name) :
    importCsv db name expected declared codecs wire = .ok next ↔
      db name = none ∧ expected = declared ∧ ∃ rows : Typed.Table declared Value,
        Typed.decode declared codecs wire = .ok rows ∧
        next = Function.update db name (some ⟨declared, rows⟩) :=
  Proofs.Formats.Csv.NamedTable.importCsv_ok_iff db next name

theorem importCsv_preserves_other [DecidableEq Name] [DecidableEq Kind]
    {db next : Packed Name Field Value} {name other : Name}
    (ok : importCsv db name expected declared codecs wire = .ok next) (different : other ≠ name) :
    next other = db other := by
  obtain ⟨_, _, rows, _, rfl⟩ := (importCsv_ok_iff db next name).mp ok
  exact Function.update_of_ne different _ _

/-- A successful named export carries its original schema, and decoding its
bytes recovers the ordered rows under the caller's parse-after-print law. -/
theorem decode_exportCsv (db : Packed Name Field Value) (name : Name)
    {table : Scan.Observation Field Value} (found : Scan.observePacked db name = some table)
    (law : ∀ k, (codecs k).ParsePrint)
    (written : exportCsv db name codecs = .ok (declared, wire)) :
    declared = table.schema ∧ Typed.decode table.schema codecs wire = .ok table.rows :=
  Proofs.Formats.Csv.NamedTable.decode_exportCsv db name found law written

theorem import_exportCsv [DecidableEq Name] [DecidableEq Kind]
    (source target : Packed Name Field Value) (exportName dest : Name)
    {table : Scan.Observation Field Value} (found : Scan.observePacked source exportName = some table)
    (vacant : target dest = none) (law : ∀ k, (codecs k).ParsePrint)
    (written : exportCsv source exportName codecs = .ok (declared, wire)) :
    importCsv target dest table.schema declared codecs wire =
      .ok (Function.update target dest (some ⟨table.schema, table.rows⟩)) := by
  obtain ⟨rfl, decoded⟩ := decode_exportCsv source exportName found law written
  exact (importCsv_ok_iff target _ dest).mpr ⟨vacant, rfl, table.rows, decoded, rfl⟩

theorem csv_of_importArrow [DecidableEq Name] [DecidableEq Kind]
    {db loaded : Packed Name Field Value} {name : Name}
    {stream : Events.EventStream Field Value Error}
    (loadedOk : importArrow db name expected stream = .ok loaded)
    (law : ∀ k, (codecs k).ParsePrint)
    (written : exportCsv loaded name codecs = .ok (declared, wire)) :
    ∃ rows : Typed.Table expected Value, stream.collect = .ok ⟨⟨expected, rows⟩, .eos⟩ ∧
      declared = expected ∧ Typed.decode expected codecs wire = .ok rows := by
  obtain ⟨rows, collected, found⟩ := importArrow_observe loadedOk
  exact ⟨rows, collected, decode_exportCsv loaded name found law written⟩

theorem csv_of_importParquet [DecidableEq Name] [DecidableEq Kind]
    {db loaded : Packed Name Field Value} {name : Name}
    {opened : Reader.OpenResult Group Field Value Error}
    (loadedOk : importParquet db name expected opened = .ok loaded)
    (law : ∀ k, (codecs k).ParsePrint)
    (written : exportCsv loaded name codecs = .ok (declared, wire)) :
    ∃ rows : Typed.Table expected Value, Reader.denote opened = .ok ⟨⟨expected, rows⟩, .eos⟩ ∧
      declared = expected ∧ Typed.decode expected codecs wire = .ok rows := by
  rw [← Reader.collect_readAll opened]
  exact csv_of_importArrow loadedOk law written

end Silmaril.Formats.Csv.NamedTable
