module

public import Silmaril.Formats.Arrow.FromCsv.Defs
import Silmaril.Proofs.Formats.Arrow.FromCsv
import Silmaril.Formats.Arrow.Writer.Thms

/-! The checked adapter preserves schema, row count and ordered nullable cells. -/

public section

namespace Silmaril.Formats.Arrow.FromCsv

open Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (Packed)
open ToCsv (Cell schemaOf eraseRow codecs)

theorem ofRows_preserves {fields : List Field} {rows : Scan.Table (schemaOf fields) Cell}
    {input : Writer.BatchInput} (checked : ofRows fields rows = .ok input) :
    input.fields = fields ∧ input.rowCount = rows.length ∧ input.observe = rows.map (eraseRow fields) :=
  Proofs.Formats.Arrow.FromCsv.ofRows_preserves checked

theorem ofCsv_preserves {fields : List Field} {wire : Csv.Bytes} {input : Writer.BatchInput}
    (checked : ofCsv fields wire = .ok input) :
    ∃ rows : Scan.Table (schemaOf fields) Cell,
      Csv.Typed.decode (schemaOf fields) codecs wire = .ok rows ∧
      input.fields = fields ∧ input.rowCount = rows.length ∧ input.observe = rows.map (eraseRow fields) :=
  Proofs.Formats.Arrow.FromCsv.ofCsv_preserves checked

theorem ofNamed_preserves {Name : Type} {db : Packed Name Csv.Field Cell} {name : Name}
    {fields : List Field} {input : Writer.BatchInput} (checked : ofNamed db name fields = .ok input) :
    ∃ rows : Scan.Table (schemaOf fields) Cell,
      Scan.observePacked db name = some ⟨schemaOf fields, rows⟩ ∧
      input.fields = fields ∧ input.rowCount = rows.length ∧ input.observe = rows.map (eraseRow fields) :=
  Proofs.Formats.Arrow.FromCsv.ofNamed_preserves checked

/-- Reading the successfully emitted physical batch returns the ordered source rows. -/
theorem emitBatch_roundTrip {fields : List Field} {rows : Scan.Table (schemaOf fields) Cell}
    {input : Writer.BatchInput} {limits : ObservationLimits} {frame : BatchFrame input.fields}
    (checked : ofRows fields rows = .ok input) (written : Writer.emitBatch limits input = .ok frame) :
    frame.metadata.rowCount = rows.length ∧ decodeBatch limits frame = .ok (rows.map (eraseRow fields)) := by
  obtain ⟨_, count, observed⟩ := ofRows_preserves checked
  obtain ⟨frameCount, _, decoded⟩ := Writer.emitBatch_roundtrip written
  exact ⟨frameCount.trans count, decoded.trans (congrArg Except.ok observed)⟩

end Silmaril.Formats.Arrow.FromCsv
