module

public import Silmaril.Formats.Csv.EventStream.Defs
import Silmaril.Formats.Csv.NamedTable.Utf8.Thms
import Silmaril.Formats.Csv.Typed.Utf8.Thms
import Silmaril.Formats.Relational.NamedTable.Thms

public section

namespace Silmaril.Proofs.Formats.Csv.EventStream

open Silmaril.Relational Silmaril.Formats.Csv
open Silmaril.Formats.Csv.EventStream
open Silmaril.Formats.Arrow
open Silmaril.Formats.Relational.NamedTable (Packed importCollected importCollected_ok_iff)

variable {Name Kind SourceError : Type*} {Value : Kind → Type*}
variable [DecidableEq Name]
variable {db : Packed Name Field Value} {name : Name} {expected : Typed.Schema Kind}
variable {codecs : (kind : Kind) → Typed.CellCodec (Value kind)}
variable {collected : Except SourceError (Events.Observation Field Value SourceError)}

private theorem export_inserted (rows : Typed.Table expected Value) :
    NamedTable.Utf8.exportCsv (Function.update db name (some ⟨expected, rows⟩)) name codecs =
      ((Typed.Utf8.encode expected codecs rows).map (fun wire => (expected, wire))).mapError
        NamedTable.ExportError.encodeError :=
  NamedTable.Utf8.exportCsv_of_observe
    (db := Function.update db name (some ⟨expected, rows⟩)) (name := name) (table := ⟨expected, rows⟩)
    (by simp [Scan.observePacked, Database.Packed.erase, Database.Partial.map])

variable [DecidableEq Kind]

theorem convertCollected_ok_iff (result : Result Name Value) :
    convertCollected db name expected codecs collected = .ok result ↔
      db name = none ∧ ∃ (rows : Typed.Table expected Value) (wire : Bytes),
        collected = .ok ⟨⟨expected, rows⟩, .eos⟩ ∧
        Typed.Utf8.encode expected codecs rows = .ok wire ∧
        result = ⟨Function.update db name (some ⟨expected, rows⟩), expected, wire⟩ := by
  constructor
  · intro converted
    cases h : importCollected db name expected collected with
    | error error => simp [convertCollected, h] at converted
    | ok loaded =>
      obtain ⟨vacant, rows, complete, rfl⟩ := (importCollected_ok_iff db loaded name expected collected).mp h
      simp only [convertCollected, h] at converted
      rw [export_inserted] at converted
      cases encoded : Typed.Utf8.encode expected codecs rows with
      | error error => simp [encoded, Except.map, Except.mapError] at converted
      | ok wire =>
        simp only [encoded, Except.map, Except.mapError, Except.ok.injEq] at converted
        exact ⟨vacant, rows, wire, complete, encoded, converted.symm⟩
  · rintro ⟨vacant, rows, wire, complete, encoded, rfl⟩
    have loaded := (importCollected_ok_iff db _ name expected collected).mpr ⟨vacant, rows, complete, rfl⟩
    simp [convertCollected, loaded, export_inserted, encoded, Except.map, Except.mapError]

theorem convertCollected_roundTrip {result : Result Name Value}
    (law : ∀ k, (codecs k).ParsePrint) (converted : convertCollected db name expected codecs collected = .ok result) :
    ∃ rows : Typed.Table expected Value,
      collected = .ok ⟨⟨expected, rows⟩, .eos⟩ ∧ result.schema = expected ∧
      Typed.Utf8.decode expected codecs result.wire = .ok rows ∧
      result.db = Function.update db name (some ⟨expected, rows⟩) := by
  obtain ⟨_, rows, _, complete, encoded, rfl⟩ := (convertCollected_ok_iff result).mp converted
  exact ⟨rows, complete, rfl, Typed.Utf8.decode_encode law encoded, rfl⟩

theorem convertCollected_open_error (vacant : db name = none) (error : SourceError) :
    convertCollected db name expected codecs (.error error) = .error (.input (.openError error)) := by
  simp [convertCollected, importCollected, vacant]

theorem convertCollected_read_error (vacant : db name = none)
    (table : Scan.Observation Field Value) (error : SourceError) :
    convertCollected db name expected codecs (.ok ⟨table, .readError error⟩) =
      .error (.input (.readError error)) := by
  simp [convertCollected, importCollected, vacant]

theorem convertCollected_schema_mismatch (vacant : db name = none)
    (table : Scan.Observation Field Value) (different : expected ≠ table.schema) :
    convertCollected db name expected codecs
      (.ok ⟨table, (.eos : Events.Termination SourceError)⟩) = .error (.input .schemaMismatch) := by
  simp [convertCollected, importCollected, vacant, different]

theorem convertCollected_encode_error (vacant : db name = none)
    {rows : Typed.Table expected Value} {error : Typed.Error}
    (encoded : Typed.Utf8.encode expected codecs rows = .error error) :
    convertCollected db name expected codecs
      (.ok ⟨⟨expected, rows⟩, (.eos : Events.Termination SourceError)⟩) =
      .error (.output (.encodeError error)) := by
  simp [convertCollected, importCollected, vacant, export_inserted, encoded, Except.map, Except.mapError]

end Silmaril.Proofs.Formats.Csv.EventStream
