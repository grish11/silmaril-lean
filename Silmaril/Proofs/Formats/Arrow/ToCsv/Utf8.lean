module

public import Silmaril.Formats.Arrow.ToCsv.Utf8.Defs
import Silmaril.Formats.Arrow.ToCsv.Thms
import Silmaril.Formats.Csv.NamedTable.Utf8.Thms
import Silmaril.Formats.Csv.Typed.Utf8.Thms
import Silmaril.Formats.Csv.Typed.Codecs.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.ToCsv.Utf8

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.ToCsv (Cell schemaOf eraseRow typedRows typedRows_preserve importIpc importIpc_of_read)
open Silmaril.Formats.Arrow.ToCsv.Utf8 (convert)
open Silmaril.Formats.Relational.NamedTable (Packed)

private theorem codecs_parsePrint (kind : Arrow.ToCsv.Kind) : (CsvUtf8.codecs kind).ParsePrint := by
  rcases kind with ⟨type, nullable⟩
  cases type
  · exact Csv.Typed.Codecs.int32_parsePrint
  · exact Csv.Typed.Utf8.string_parsePrint

theorem convert_roundTrip {Name : Type} [DecidableEq Name] (db : Packed Name Csv.Field Cell)
    (name : Name) (limits : ObservationLimits) (input : KBytes) {observed : ObservedStream}
    {rows : Scan.Table (schemaOf observed.fields) Cell} {wire : Csv.Bytes} (vacant : db name = none)
    (read : readRows limits input = .ok observed) (checked : typedRows observed = .ok rows)
    (representable : Csv.Typed.Utf8.encode (schemaOf observed.fields) CsvUtf8.codecs rows = .ok wire) :
    convert db name (schemaOf observed.fields) limits input =
      .ok (Function.update db name (some ⟨schemaOf observed.fields, rows⟩), schemaOf observed.fields, wire) ∧
      (Csv.Typed.Utf8.decode (schemaOf observed.fields) CsvUtf8.codecs wire).map
        (List.map (eraseRow observed.fields)) = .ok observed.batches.flatten := by
  let loaded := Function.update db name (some ⟨schemaOf observed.fields, rows⟩)
  have found : Scan.observePacked loaded name = some ⟨schemaOf observed.fields, rows⟩ := by
    simp [loaded, Scan.observePacked, Database.Packed.erase, Database.Partial.map]
  have written : Csv.NamedTable.Utf8.exportCsv loaded name CsvUtf8.codecs =
      .ok (schemaOf observed.fields, wire) := by
    simp [Csv.NamedTable.Utf8.exportCsv, found, representable]
  refine ⟨?_, ?_⟩
  · have imported : importIpc db name (schemaOf observed.fields) limits input = .ok loaded :=
      importIpc_of_read db name limits input vacant read checked
    simp [convert, imported, written, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl
  · obtain ⟨_, decoded⟩ := Csv.NamedTable.Utf8.decode_exportCsv loaded name found codecs_parsePrint written
    rw [decoded]
    exact congrArg (Except.ok (ε := Csv.Typed.Error)) (typedRows_preserve checked)

theorem convert_encodeError {Name : Type} [DecidableEq Name] (db : Packed Name Csv.Field Cell)
    (name : Name) (limits : ObservationLimits) (input : KBytes) {observed : ObservedStream}
    {rows : Scan.Table (schemaOf observed.fields) Cell} {error : Csv.Typed.Error} (vacant : db name = none)
    (read : readRows limits input = .ok observed) (checked : typedRows observed = .ok rows)
    (rejected : Csv.Typed.Utf8.encode (schemaOf observed.fields) CsvUtf8.codecs rows = .error error) :
    convert db name (schemaOf observed.fields) limits input = .error (.output (.encodeError error)) := by
  simp [convert, importIpc_of_read db name limits input vacant read checked, Csv.NamedTable.Utf8.exportCsv,
    Scan.observePacked, Database.Packed.erase, Database.Partial.map, rejected, Except.mapError,
    Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Arrow.ToCsv.Utf8
