module

public import Silmaril.Formats.Arrow.ToCsv.Defs
import Silmaril.Proofs.Formats.Arrow.ToCsv
import Silmaril.Formats.Relational.NamedTable.Thms

/-! Lossless schema translation and ordered nullable-row preservation. -/

public section

namespace Silmaril.Formats.Arrow.ToCsv

open Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (Packed importCollected)

theorem labelOf_injective : Function.Injective labelOf :=
  Proofs.Formats.Arrow.ToCsv.labelOf_injective

/-- The full schema preserves field positions, UTF-8 labels, kinds and nullability. -/
theorem schemaOf_injective : Function.Injective schemaOf :=
  Proofs.Formats.Arrow.ToCsv.schemaOf_injective

theorem typedRow_preserves {fields : List Field} {raw : Row} {row : Scan.Row (schemaOf fields) Cell}
    (checked : typedRow fields raw = .ok row) : eraseRow fields row = raw :=
  Proofs.Formats.Arrow.ToCsv.typedRow_preserves checked

theorem typedRows_preserve {observed : ObservedStream}
    {rows : Scan.Table (schemaOf observed.fields) Cell}
    (checked : typedRows observed = .ok rows) :
    rows.map (eraseRow observed.fields) = observed.batches.flatten :=
  Proofs.Formats.Arrow.ToCsv.typedRows_preserve checked

theorem codecs_parsePrint (kind : Kind) : (codecs kind).ParsePrint :=
  Proofs.Formats.Arrow.ToCsv.codecs_parsePrint kind

theorem importIpc_of_read {Name : Type} [DecidableEq Name] (db : Packed Name Csv.Field Cell)
    (name : Name) (limits : ObservationLimits) (input : KBytes) {observed : ObservedStream}
    {rows : Scan.Table (schemaOf observed.fields) Cell} (vacant : db name = none)
    (read : readRows limits input = .ok observed) (checked : typedRows observed = .ok rows) :
    importIpc db name (schemaOf observed.fields) limits input =
      .ok (Function.update db name (some ⟨schemaOf observed.fields, rows⟩)) :=
  Proofs.Formats.Arrow.ToCsv.importIpc_of_read db name limits input vacant read checked

/-- At a vacant destination, reader errors are preserved without an insertion. -/
theorem importIpc_byteError {Name : Type} [DecidableEq Name] (db : Packed Name Csv.Field Cell)
    (name : Name) (expected : Csv.Typed.Schema Kind) (limits : ObservationLimits) (input : KBytes)
    {error : Error} (vacant : db name = none) (read : readRows limits input = .error error) :
    importIpc db name expected limits input = .error (.openError (.ipc error)) := by
  simp [importIpc, observeIpc, importCollected, vacant, read, Except.mapError, Bind.bind, Except.bind]

/-- When the observed rows are representable by the typed CSV encoder, the
bridge emits their schema and bytes. Decoding them recovers the source rows in
exact order, including null cells and rows at width zero. -/
theorem convert_roundTrip {Name : Type} [DecidableEq Name] (db : Packed Name Csv.Field Cell)
    (name : Name) (limits : ObservationLimits) (input : KBytes) {observed : ObservedStream}
    {rows : Scan.Table (schemaOf observed.fields) Cell} {wire : Csv.Bytes} (vacant : db name = none)
    (read : readRows limits input = .ok observed) (checked : typedRows observed = .ok rows)
    (representable : Csv.Typed.encode (schemaOf observed.fields) codecs rows = .ok wire) :
    convert db name (schemaOf observed.fields) limits input = .ok (schemaOf observed.fields, wire) ∧
      (Csv.Typed.decode (schemaOf observed.fields) codecs wire).map
        (List.map (eraseRow observed.fields)) = .ok observed.batches.flatten :=
  Proofs.Formats.Arrow.ToCsv.convert_roundTrip db name limits input vacant read checked representable

end Silmaril.Formats.Arrow.ToCsv
