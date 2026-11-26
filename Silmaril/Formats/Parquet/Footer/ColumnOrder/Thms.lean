module

public import Silmaril.Formats.Parquet.Footer.ColumnOrder.Defs
import Silmaril.Proofs.Formats.Parquet.Footer.ColumnOrder.Correctness

public section

namespace Silmaril.Formats.Parquet.Footer.ColumnOrder

open ThriftCompact
open Traversal (Reader Field)

theorem readStructList_erase {ε : Type} (reader : Reader) (field : Field) (fail : Error → ε) :
    ((readStructList reader field).map (List.map Item.fields)).mapError fail = (do
      if field.type ≠ .payload .list then throw (fail (.fieldType field.id))
      let (items, next) ← Traversal.readList reader (fail ∘ Error.compact) .struct
        (fun offset => (Traversal.readStruct reader offset).mapError (fail ∘ Error.compact))
        field.start
      if next ≠ field.stop then throw (fail (.fieldExtent field.id))
      pure items) :=
  Proofs.Formats.Parquet.Footer.ColumnOrder.readStructList_erase reader field fail

theorem readSelection_wire {limits : Footer.Limits} {snapshot : Snapshot.Checked}
    {column : Nat} {result : Selection}
    (h : readSelection limits snapshot column = .ok result) :
    SelectionWire limits snapshot column result :=
  Proofs.Formats.Parquet.Footer.ColumnOrder.readSelection_wire h

theorem readMarker_sound {reader : Reader} {item : Item} {marker : Marker}
    (h : readMarker reader item = .ok marker) : MarkerWire reader item marker :=
  Proofs.Formats.Parquet.Footer.ColumnOrder.readMarker_sound h

/-- The typed leaf and exact raw items use the original serialized schema
and leaf-order ordinals of the same checked footer. -/
theorem readFlat_wire {limits : Footer.Limits} {snapshot : Snapshot.Checked}
    {column : Nat} {result : FlatLeaf} (h : readFlat limits snapshot column = .ok result) :
    FlatWire limits snapshot column result :=
  Proofs.Formats.Parquet.Footer.ColumnOrder.readFlat_wire h

end Silmaril.Formats.Parquet.Footer.ColumnOrder
