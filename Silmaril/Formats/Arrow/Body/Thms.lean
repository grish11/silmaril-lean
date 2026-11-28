module

public import Silmaril.Formats.Arrow.Body.Defs
import Silmaril.Proofs.Formats.Arrow.Body

@[expose] public section

namespace Silmaril.Formats.Arrow

theorem Body.validAt_iff (bitmap : KBytes) (wf : bitmap.wf = true) (index : Nat) (valid : Bool) :
    Body.validAt bitmap index = some valid ↔
      if bitmap.toList.isEmpty then valid = true
      else ∃ byte, bitmap.toList[index / 8]? = some byte ∧
        valid = byte.toNat.testBit (index % 8) :=
  Proofs.Formats.Arrow.validAt_iff bitmap wf index valid

theorem Body.offsetAt_iff (offsets : KBytes) (index value : Nat) :
    Body.offsetAt offsets index = some value ↔
      offsets.readLE (4 * index) 4 = some value ∧ value < 2^31 :=
  Proofs.Formats.Arrow.offsetAt_iff offsets index value

theorem Body.readCell_iff (buffers : Body.ColumnBuffers) (index : Nat) (value : Option Value) :
    Body.readCell buffers index = .ok value ↔ Body.CellWire buffers index value :=
  Proofs.Formats.Arrow.readCell_iff buffers index value

theorem Body.readColumn_iff (node : FieldNode) (buffers : Body.ColumnBuffers) (values : Column) :
    Body.readColumn node buffers = .ok values ↔ Body.ColumnWire node buffers values :=
  Proofs.Formats.Arrow.readColumn_iff node buffers values

/-- The returned rows are exactly the ordered observation of checked buffers,
provided that the frame passes the source and allocation guards. -/
theorem decodeBatch_iff (limits : ObservationLimits) {fields : List Field}
    (frame : BatchFrame fields) (rows : List Row) :
    decodeBatch limits frame = .ok rows ↔ Body.checkBatch limits frame = .ok () ∧ BatchWire frame rows :=
  Proofs.Formats.Arrow.decodeBatch_iff limits frame rows

theorem BatchWire.shape {fields : List Field} {frame : BatchFrame fields} {rows : List Row}
    (wire : BatchWire frame rows) :
    rows.length = frame.metadata.rowCount ∧ ∀ row ∈ rows, row.length = fields.length :=
  Proofs.Formats.Arrow.BatchWire.shape wire

end Silmaril.Formats.Arrow
