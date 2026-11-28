module

public import Silmaril.Formats.Arrow.ToCsv.Utf8.Defs
import Silmaril.Proofs.Formats.Arrow.ToCsv.Utf8
import Silmaril.Formats.Arrow.ToCsv.Thms

/-! Exact named update and nullable-row preservation through UTF-8 CSV. -/

public section

namespace Silmaril.Formats.Arrow.ToCsv.Utf8

open Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (Packed)

/-- For a vacant destination and a complete checked IPC read, successful CSV
encoding returns the exact named update and the bytes of the flattened table. -/
theorem convert_roundTrip {Name : Type} [DecidableEq Name] (db : Packed Name Csv.Field Cell)
    (name : Name) (limits : ObservationLimits) (input : KBytes) {observed : ObservedStream}
    {rows : Scan.Table (schemaOf observed.fields) Cell} {wire : Csv.Bytes} (vacant : db name = none)
    (read : readRows limits input = .ok observed) (checked : typedRows observed = .ok rows)
    (representable : Csv.Typed.Utf8.encode (schemaOf observed.fields) CsvUtf8.codecs rows = .ok wire) :
    convert db name (schemaOf observed.fields) limits input =
      .ok (Function.update db name (some ⟨schemaOf observed.fields, rows⟩), schemaOf observed.fields, wire) ∧
      (Csv.Typed.Utf8.decode (schemaOf observed.fields) CsvUtf8.codecs wire).map
        (List.map (eraseRow observed.fields)) = .ok observed.batches.flatten :=
  Proofs.Formats.Arrow.ToCsv.Utf8.convert_roundTrip db name limits input vacant read checked representable

/-- At a vacant destination, an IPC read error returns without a named update. -/
theorem convert_byteError {Name : Type} [DecidableEq Name] (db : Packed Name Csv.Field Cell)
    (name : Name) (expected : Csv.Typed.Schema Kind) (limits : ObservationLimits) (input : KBytes)
    {error : Error} (vacant : db name = none) (read : readRows limits input = .error error) :
    convert db name expected limits input = .error (.input (.openError (.ipc error))) := by
  simp [convert, importIpc_byteError db name expected limits input vacant read, Except.mapError,
    Bind.bind, Except.bind]

/-- A UTF-8 CSV encoder error prevents the staged database from being returned. -/
theorem convert_encodeError {Name : Type} [DecidableEq Name] (db : Packed Name Csv.Field Cell)
    (name : Name) (limits : ObservationLimits) (input : KBytes) {observed : ObservedStream}
    {rows : Scan.Table (schemaOf observed.fields) Cell} {error : Csv.Typed.Error} (vacant : db name = none)
    (read : readRows limits input = .ok observed) (checked : typedRows observed = .ok rows)
    (rejected : Csv.Typed.Utf8.encode (schemaOf observed.fields) CsvUtf8.codecs rows = .error error) :
    convert db name (schemaOf observed.fields) limits input = .error (.output (.encodeError error)) :=
  Proofs.Formats.Arrow.ToCsv.Utf8.convert_encodeError db name limits input vacant read checked rejected

end Silmaril.Formats.Arrow.ToCsv.Utf8
