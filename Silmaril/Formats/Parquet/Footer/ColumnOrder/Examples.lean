module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Footer.ColumnOrder.Thms
import Silmaril.Formats.Parquet.ColumnIndex.Signed.Compatibility.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Footer.ColumnOrder.Defs
meta import Silmaril.Formats.Parquet.ColumnIndex.Signed.Defs

/-! Pinned two-leaf producer and Compact footer mutations. -/

namespace Silmaril.Formats.Parquet.Footer.ColumnOrder

private def fixture : Bytes := ⟨include_bytes "../../../../../data/parquet-footer-column-order/two-leaves.parquet"⟩

private def orderFixture (wire : List UInt8) : Bytes :=
  let footerStart := 242
  let orderStart := 788
  let footerLength := orderStart - footerStart + wire.length + 1
  (Footer.fileBytes fixture 0 orderStart).append
    (Bytes.ofList (wire ++ [0] ++ KBytes.unpack 4 footerLength ++ [80, 65, 82, 49]))

private def changedSecond (tag : UInt8) : Bytes :=
  orderFixture [0x19, 0x2c, 0x1c, 0, 0, tag * 16 + 12, 0, 0]

private def absent : Bytes := orderFixture []
private def short : Bytes := orderFixture [0x19, 0x1c, 0x1c, 0, 0]
private def surplus : Bytes := orderFixture [0x19, 0x3c, 0x1c, 0, 0, 0x1c, 0, 0, 0x1c, 0, 0]
private def duplicate : Bytes :=
  orderFixture [0x19, 0x2c, 0x1c, 0, 0, 0x1c, 0, 0, 0x09, 14, 0x2c, 0x1c, 0, 0, 0x1c, 0, 0]
private def badField : Bytes := orderFixture [0x15, 0]
private def badElement : Bytes := orderFixture [0x19, 0x21, 1, 1]
private def emptyUnion : Bytes := orderFixture [0x19, 0x2c, 0x1c, 0, 0, 0]
private def multipleArms : Bytes := orderFixture [0x19, 0x2c, 0x1c, 0, 0, 0x1c, 0, 0x1c, 0, 0]
private def nonemptyMarker : Bytes := orderFixture [0x19, 0x2c, 0x1c, 0, 0, 0x1c, 0x11, 0, 0]
private def unsupportedWrongType : Bytes := orderFixture [0x19, 0x2c, 0x21, 0, 0x1c, 0, 0]

private structure Observed where
  name : String
  schemaList : Footer.Span
  schemaItem : Footer.Span
  orderExtent : Option (Footer.Span × Footer.Span)
  marker : Option Marker
  converted : Option Int
  logicalTag : Option Int
  deriving DecidableEq

private def extent (slot : Slot) : Footer.Span × Footer.Span :=
  (⟨slot.container.start, slot.container.stop⟩, ⟨slot.item.start, slot.item.stop⟩)

private def observe (source : Bytes) (column : Nat) (limits : Footer.Limits := {}) :
    Option (Except Error Observed) := do
  let snapshot ← (Snapshot.check (Failure := Unit) {} source).toOption
  pure <| do
    let leaf ← readFlat limits snapshot column
    let (schemaList, schemaItem) := extent leaf.selection.leaf
    let converted ← leaf.convertedType
    let logical ← leaf.logicalMember
    pure ⟨leaf.leaf.name, schemaList, schemaItem, leaf.selection.order.map extent, leaf.order,
      converted, logical.map (·.id)⟩

private def signedLeaf : Observed :=
  ⟨"signed", ⟨3, 54⟩, ⟨17, 30⟩, some (⟨547, 554⟩, ⟨548, 551⟩), some .typeOrder, none, none⟩

private def unsignedLeaf : Observed :=
  ⟨"unsigned", ⟨3, 54⟩, ⟨30, 54⟩, some (⟨547, 554⟩, ⟨551, 554⟩), some .typeOrder, some 13, some 10⟩

#guard observe fixture 0 = some (.ok signedLeaf)
#guard observe fixture 1 = some (.ok unsignedLeaf)
#guard observe (changedSecond 2) 0 = some (.ok signedLeaf)
#guard observe (changedSecond 2) 1 = some (.ok { unsignedLeaf with marker := some .ieee754TotalOrder })
#guard observe (changedSecond 3) 1 = some (.ok { unsignedLeaf with marker := some .int96TimestampOrder })
#guard observe (changedSecond 4) 1 = some (.ok { unsignedLeaf with marker := some (.unknown 4) })
#guard observe absent 1 = some (.ok { unsignedLeaf with marker := none, orderExtent := none })
#guard observe short 0 = some (.error (.orderCount 2 1))
#guard observe surplus 1 = some (.error (.orderCount 2 3))
#guard observe duplicate 0 = some (.error (.duplicateField 7))
#guard observe badField 1 = some (.error (.fieldType 7))
#guard observe badElement 1 = some (.error (.compact (.elementType .struct .bool)))
#guard observe emptyUnion 1 = some (.error .orderUnion)
#guard observe multipleArms 1 = some (.error .orderUnion)
#guard observe nonemptyMarker 1 = some (.error (.markerPayload 1))
#guard observe unsupportedWrongType 0 = some (.error (.fieldType 2))
#guard observe fixture 2 = some (.error (.leafOrdinal 3))
#guard observe fixture 0 { maxFooterBytes := 554 } = some (.error .footerByteLimit)

private def signedGate (source : Bytes) (name : String) :
    Option (Except ColumnIndex.Signed.OrderError Unit) := do
  let snapshot ← (Snapshot.check (Failure := Unit) {} source).toOption
  let bound ← (FlatColumn.bindColumn snapshot ⟨name, .int32, .optional⟩).toOption
  pure (ColumnIndex.Signed.checkOrder {} snapshot bound)

-- Earlier structural causes take precedence over annotation presence.
#guard signedGate absent "unsigned" = some (.error .missingOrder)
#guard signedGate short "unsigned" = some (.error .footerShape)
#guard signedGate badElement "unsigned" = some (.error (.compact (.elementType .struct .bool)))
-- The selected annotation precedes the union payload, and the arm tag precedes its type.
#guard signedGate multipleArms "unsigned" = some (.error .annotated)
#guard signedGate unsupportedWrongType "signed" = some (.error .unsupportedOrder)
#guard signedGate fixture "signed" = some (.ok ())

end Silmaril.Formats.Parquet.Footer.ColumnOrder
