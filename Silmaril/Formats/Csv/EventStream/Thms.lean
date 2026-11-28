module

public import Silmaril.Formats.Csv.EventStream.Defs
import Silmaril.Proofs.Formats.Csv.EventStream
import Silmaril.Formats.Parquet.Reader.Thms

/-! Exact success and failure contracts for typed events to UTF-8 CSV. -/

public section

namespace Silmaril.Formats.Csv.EventStream

open Silmaril.Relational
open Silmaril.Formats.Arrow
open Silmaril.Formats.Parquet
open Silmaril.Formats.Relational.NamedTable (Packed)

variable {Name Kind SourceError Group : Type*} {Value : Kind → Type*}
variable [DecidableEq Name] [DecidableEq Kind]
variable {db : Packed Name Field Value} {name : Name} {expected : Typed.Schema Kind}
variable {codecs : (kind : Kind) → Typed.CellCodec (Value kind)}
variable {collected : Except SourceError (Events.Observation Field Value SourceError)}

/-- Success requires exact-schema EOS, a vacant name, and a successful byte export. -/
theorem convertCollected_ok_iff (result : Result Name Value) :
    convertCollected db name expected codecs collected = .ok result ↔
      db name = none ∧ ∃ (rows : Typed.Table expected Value) (wire : Bytes),
        collected = .ok ⟨⟨expected, rows⟩, .eos⟩ ∧
        Typed.Utf8.encode expected codecs rows = .ok wire ∧
        result = ⟨Function.update db name (some ⟨expected, rows⟩), expected, wire⟩ :=
  Proofs.Formats.Csv.EventStream.convertCollected_ok_iff result

/-- Decoding the resulting bytes recovers the EOS observation's ordered table. -/
theorem convertCollected_roundTrip {result : Result Name Value}
    (law : ∀ k, (codecs k).ParsePrint) (converted : convertCollected db name expected codecs collected = .ok result) :
    ∃ rows : Typed.Table expected Value,
      collected = .ok ⟨⟨expected, rows⟩, .eos⟩ ∧ result.schema = expected ∧
      Typed.Utf8.decode expected codecs result.wire = .ok rows ∧
      result.db = Function.update db name (some ⟨expected, rows⟩) :=
  Proofs.Formats.Csv.EventStream.convertCollected_roundTrip law converted

/-- A completed Arrow event conversion preserves all rows in batch order. -/
theorem convert_roundTrip {stream : Events.EventStream Field Value SourceError} {result : Result Name Value}
    (law : ∀ k, (codecs k).ParsePrint) (converted : convert db name expected codecs stream = .ok result) :
    ∃ rows : Typed.Table expected Value,
      stream.collect = .ok ⟨⟨expected, rows⟩, .eos⟩ ∧ result.schema = expected ∧
      Typed.Utf8.decode expected codecs result.wire = .ok rows ∧
      result.db = Function.update db name (some ⟨expected, rows⟩) :=
  convertCollected_roundTrip law converted

/-- Parquet conversion uses the full ordered row-group denotation, including its terminal outcome. -/
theorem convertParquet_eq_denote (opened : Reader.OpenResult Group Field Value SourceError) :
    convertParquet db name expected codecs opened = convertCollected db name expected codecs (Reader.denote opened) :=
  congrArg (convertCollected db name expected codecs) (Reader.collect_readAll opened)

/-- A completed Parquet conversion preserves the ordered full-read denotation. -/
theorem convertParquet_roundTrip {opened : Reader.OpenResult Group Field Value SourceError}
    {result : Result Name Value} (law : ∀ k, (codecs k).ParsePrint)
    (converted : convertParquet db name expected codecs opened = .ok result) :
    ∃ rows : Typed.Table expected Value,
      Reader.denote opened = .ok ⟨⟨expected, rows⟩, .eos⟩ ∧ result.schema = expected ∧
      Typed.Utf8.decode expected codecs result.wire = .ok rows ∧
      result.db = Function.update db name (some ⟨expected, rows⟩) := by
  rw [convertParquet_eq_denote] at converted
  exact convertCollected_roundTrip law converted

/-- Open failure at a vacant name returns the input error alone. -/
theorem convertCollected_open_error (vacant : db name = none) (error : SourceError) :
    convertCollected db name expected codecs (.error error) = .error (.input (.openError error)) :=
  Proofs.Formats.Csv.EventStream.convertCollected_open_error vacant error

/-- Read failure returns its error even when the observation contains earlier rows. -/
theorem convertCollected_read_error (vacant : db name = none)
    (table : Scan.Observation Field Value) (error : SourceError) :
    convertCollected db name expected codecs (.ok ⟨table, .readError error⟩) =
      .error (.input (.readError error)) :=
  Proofs.Formats.Csv.EventStream.convertCollected_read_error vacant table error

/-- A mismatched schema at EOS returns a schema error. -/
theorem convertCollected_schema_mismatch (vacant : db name = none)
    (table : Scan.Observation Field Value) (different : expected ≠ table.schema) :
    convertCollected db name expected codecs
      (.ok ⟨table, (.eos : Events.Termination SourceError)⟩) = .error (.input .schemaMismatch) :=
  Proofs.Formats.Csv.EventStream.convertCollected_schema_mismatch vacant table different

/-- An encoding failure after successful insertion returns only the output error. -/
theorem convertCollected_encode_error (vacant : db name = none)
    {rows : Typed.Table expected Value} {error : Typed.Error}
    (encoded : Typed.Utf8.encode expected codecs rows = .error error) :
    convertCollected db name expected codecs
      (.ok ⟨⟨expected, rows⟩, (.eos : Events.Termination SourceError)⟩) =
      .error (.output (.encodeError error)) :=
  Proofs.Formats.Csv.EventStream.convertCollected_encode_error vacant encoded

end Silmaril.Formats.Csv.EventStream
