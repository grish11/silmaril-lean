module

public import Silmaril.Formats.Arrow.TimestampStream.ToCsv.Defs
import Silmaril.Formats.Csv.EventStream.Thms
import Silmaril.Formats.Csv.Typed.Codecs.Thms
import Silmaril.Formats.Csv.Typed.Utf8.Thms
import Silmaril.Numeric.Timestamp.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.TimestampStream.ToCsv

open Silmaril.Relational Silmaril.Formats Silmaril.Numeric.Timestamp
open Silmaril.Formats.Arrow.TimestampStream
open Silmaril.Formats.Arrow.TimestampStream.ToCsv
open Silmaril.Formats.Relational.NamedTable (Packed)

theorem codecs_parsePrint (kind : ToCsv.Kind) : (codecs kind).ParsePrint := by
  intro value field printed
  change (value.toInt64 kind.unit).toOption.map Csv.Typed.Codecs.int64Text = some field at printed
  cases written : value.toInt64 kind.unit with
  | error reason => simp [written, Except.toOption] at printed
  | ok payload =>
    have parsed : Csv.Typed.Codecs.parseInt64 field = some payload :=
      Csv.Typed.Codecs.int64_parsePrint (by
        change some (Csv.Typed.Codecs.int64Text payload) = some field
        simpa only [written, Except.toOption, Option.map_some] using printed)
    have denotation := Ticks.toInt64_eq_ok_iff.mp written
    have counts := congrArg (fun t => t.ticks) denotation
    simp only [Ticks.denote, Ticks.ofInt64] at counts
    have scaleNonzero : kind.unit.nanosecondsPerTick ≠ 0 := by cases kind.unit <;> decide
    have tickEq := Int.eq_of_mul_eq_mul_right scaleNonzero counts
    change (Csv.Typed.Codecs.parseInt64 field).map (Ticks.ofInt64 kind.metadata.kind kind.unit) = some value
    rw [parsed, Option.map_some]
    exact congrArg some (by cases value; cases tickEq; rfl)

variable {Name : Type*} [DecidableEq Name]
variable {db : Packed Name Csv.Field Cell} {name : Name} {ipcLimits : Arrow.Limits}
variable {csvLimits : CsvLimits} {input : KBytes}

theorem convert_of_read {stream : Stream} {wire : Csv.Bytes}
    (vacant : db name = none) (read : read ipcLimits input = .ok stream)
    (rowsFit : (rows stream).length ≤ csvLimits.maxRows)
    (encoded : Csv.Typed.Utf8.encode (schemaOf stream.binding) codecs (rows stream) = .ok wire)
    (bytesFit : wire.length ≤ csvLimits.maxBytes) :
    convert db name ipcLimits csvLimits input =
      .ok ⟨Function.update db name (some ⟨schemaOf stream.binding, rows stream⟩), schemaOf stream.binding, wire⟩ := by
  have exported : Csv.EventStream.convertCollected (SourceError := Arrow.TimestampStream.Error)
      db name (schemaOf stream.binding) codecs (.ok ⟨⟨schemaOf stream.binding, rows stream⟩, .eos⟩) =
      .ok ⟨Function.update db name (some ⟨schemaOf stream.binding, rows stream⟩), schemaOf stream.binding, wire⟩ :=
    (Csv.EventStream.convertCollected_ok_iff _).mpr ⟨vacant, _, wire, rfl, encoded, rfl⟩
  simp [convert, vacant, read, exported, Nat.not_lt_of_ge rowsFit, Nat.not_lt_of_ge bytesFit]

theorem convert_readback {result : Csv.EventStream.Result Name Cell}
    (converted : convert db name ipcLimits csvLimits input = .ok result) :
    db name = none ∧ ∃ stream : Stream,
      read ipcLimits input = .ok stream ∧
      result.schema = schemaOf stream.binding ∧
      result.db = Function.update db name (some ⟨schemaOf stream.binding, rows stream⟩) ∧
      Csv.Typed.Utf8.decode (schemaOf stream.binding) codecs result.wire = .ok (rows stream) ∧
      (rows stream).length ≤ csvLimits.maxRows ∧ result.wire.length ≤ csvLimits.maxBytes := by
  cases occupied : db name with
  | some current => simp [convert, occupied] at converted
  | none =>
    simp only [convert, occupied, Option.isSome_none, Bool.false_eq_true, ite_false] at converted
    cases reading : read ipcLimits input with
    | error reason => simp [reading] at converted
    | ok stream =>
      simp only [reading] at converted
      split at converted
      next cap => cases converted
      next rowsFit =>
        cases encoded : Csv.EventStream.convertCollected (SourceError := Arrow.TimestampStream.Error)
            db name (schemaOf stream.binding) codecs (.ok ⟨⟨schemaOf stream.binding, rows stream⟩, .eos⟩) with
        | error reason => simp [encoded] at converted
        | ok exported =>
          simp only [encoded] at converted
          split at converted
          next cap => cases converted
          next bytesFit =>
            cases converted
            obtain ⟨_, exportedRows, wire, observed, written, rfl⟩ :=
              (Csv.EventStream.convertCollected_ok_iff _).mp encoded
            have sameRows : rows stream = exportedRows := eq_of_heq
              (Scan.Observation.mk.inj (congrArg Arrow.Events.Observation.table (Except.ok.inj observed))).2
            subst exportedRows
            exact ⟨rfl, stream, rfl, rfl, rfl, Csv.Typed.Utf8.decode_encode codecs_parsePrint written,
              Nat.le_of_not_gt rowsFit, Nat.le_of_not_gt bytesFit⟩

end Silmaril.Proofs.Formats.Arrow.TimestampStream.ToCsv
