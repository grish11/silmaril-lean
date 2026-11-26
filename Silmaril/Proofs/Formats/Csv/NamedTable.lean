module

public import Silmaril.Formats.Csv.NamedTable.Defs
import Silmaril.Formats.Csv.Typed.Thms
import Silmaril.Formats.Relational.NamedTable.Thms

public section

namespace Silmaril.Proofs.Formats.Csv.NamedTable

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Csv
open Silmaril.Formats.Csv.NamedTable
open Silmaril.Formats.Csv.NamedTable.Internal (importDecoded exportWith)
open Silmaril.Formats.Relational.NamedTable (Packed importCollected_ok_iff)

variable {Name Kind : Type*} {Value : Kind → Type*}
variable {declared expected : Typed.Schema Kind}
variable {codecs : (kind : Kind) → Typed.CellCodec (Value kind)} {wire : Bytes}

theorem collect_eventsOfBytes (declared : Typed.Schema Kind)
    (codecs : (kind : Kind) → Typed.CellCodec (Value kind)) (wire : Bytes) :
    (eventsOfBytes declared codecs wire).collect =
      (Typed.decode declared codecs wire).map (fun rows => ⟨⟨declared, rows⟩, .eos⟩) := by
  cases decoded : Typed.decode declared codecs wire <;>
    simp [eventsOfBytes, decoded, Except.map, Events.EventStream.collect, Events.Trace.collect, Events.Trace.rows]

theorem importDecoded_ok_iff [DecidableEq Name] [DecidableEq Kind]
    (db next : Packed Name Field Value) (name : Name)
    (decoded : Except Typed.Error (Typed.Table declared Value)) :
    importDecoded db name expected declared decoded = .ok next ↔
      db name = none ∧ expected = declared ∧ ∃ rows : Typed.Table declared Value,
        decoded = .ok rows ∧ next = Function.update db name (some ⟨declared, rows⟩) := by
  rw [importDecoded, importCollected_ok_iff]
  by_cases same : expected = declared
  · subst expected
    cases decoded <;> simp [Except.map]
  · cases decoded <;> simp [Except.map, same, Ne.symm same]

theorem importCsv_ok_iff [DecidableEq Name] [DecidableEq Kind]
    (db next : Packed Name Field Value) (name : Name) :
    importCsv db name expected declared codecs wire = .ok next ↔
      db name = none ∧ expected = declared ∧ ∃ rows : Typed.Table declared Value,
        Typed.decode declared codecs wire = .ok rows ∧
        next = Function.update db name (some ⟨declared, rows⟩) :=
  importDecoded_ok_iff db next name (Typed.decode declared codecs wire)

theorem exportWith_observe {db : Packed Name Field Value} {name : Name}
    {write : Scan.Observation Field Value → Except Typed.Error Bytes}
    {table : Scan.Observation Field Value} (found : Scan.observePacked db name = some table)
    (written : exportWith db name write = .ok (declared, wire)) :
    declared = table.schema ∧ write table = .ok wire := by
  unfold exportWith at written
  rw [found] at written
  cases encoded : write table with
  | error error => simp [encoded] at written
  | ok bytes =>
    have pair : (table.schema, bytes) = (declared, wire) := by simpa [encoded] using written
    rcases Prod.mk.inj pair with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem decode_exportCsv (db : Packed Name Field Value) (name : Name)
    {table : Scan.Observation Field Value} (found : Scan.observePacked db name = some table)
    (law : ∀ k, (codecs k).ParsePrint)
    (written : exportCsv db name codecs = .ok (declared, wire)) :
    declared = table.schema ∧ Typed.decode table.schema codecs wire = .ok table.rows := by
  obtain ⟨same, encoded⟩ := exportWith_observe found written
  exact ⟨same, Typed.decode_encode law encoded⟩

end Silmaril.Proofs.Formats.Csv.NamedTable
