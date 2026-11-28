module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Footer.NestedLeaf.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Footer.NestedLeaf.Defs

namespace Silmaril.Formats.Parquet.Footer.NestedLeaf

private def fixture : Bytes := ⟨include_bytes "../../../../../data/parquet-nested-footer/optional-point.parquet"⟩
private def required : Bytes := ⟨include_bytes "../../../../../data/parquet-nested-footer/required-parent.parquet"⟩
private def flat : Bytes := ⟨include_bytes "../../../../../data/parquet-footer-column-order/two-leaves.parquet"⟩

private def annotated : Bytes :=
  (Footer.fileBytes fixture 0 178).append <|
    (Bytes.ofList [0x15, 6]).append <|
    (Footer.fileBytes fixture 178 814).append (Bytes.ofList [0x9a, 2, 0, 0, 80, 65, 82, 49])

private structure Observed where
  schemaOrdinal : Nat
  columnOrdinal : Nat
  path : List String
  physical : PhysicalType
  repetition : Option Repetition
  schemaSpan : Span
  parentSpan : Span
  leafSpan : Span
  deriving DecidableEq

private def observe (source : Bytes) (column group : Nat) (limits : Limits := {}) :
    Option (Except Error Observed) := do
  let snapshot ← (Snapshot.check (Failure := Unit) {} source).toOption
  pure <| do
    let selected ← select limits snapshot column
    let (_, chunk) ← selectChunk selected group
    pure ⟨selected.schemaOrdinal, selected.columnOrdinal, chunk.metadata.pathInSchema,
      chunk.metadata.physicalType, selected.leaf.repetition,
      ⟨selected.container.start, selected.container.stop⟩,
      ⟨selected.parentItem.start, selected.parentItem.stop⟩, ⟨selected.leafItem.start, selected.leafItem.stop⟩⟩

#guard observe fixture 0 0 =
  some (.ok ⟨2, 0, ["point", "signed"], .int32, some .required, ⟨3, 53⟩, ⟨17, 29⟩, ⟨29, 42⟩⟩)
#guard observe fixture 1 0 =
  some (.ok ⟨3, 1, ["point", "wide"], .int64, some .optional, ⟨3, 53⟩, ⟨17, 29⟩, ⟨42, 53⟩⟩)

#guard observe fixture 2 0 = some (.error (.columnOrdinal 2))
#guard observe fixture 1 1 = some (.error (.groupOrdinal 1))
#guard observe fixture 0 0 { maxFooterBytes := 663 } = some (.error .footerByteLimit)
#guard observe required 0 0 = some (.error .unsupportedShape)
#guard observe flat 0 0 = some (.error .unsupportedShape)
#guard observe annotated 1 0 = some (.error .annotatedGroup)

private def flatError : Option ColumnOrder.Error := do
  let snapshot ← (Snapshot.check (Failure := Unit) {} fixture).toOption
  match ColumnOrder.readFlat {} snapshot 0 with
  | .error error => some error
  | .ok _ => none

#guard flatError = some .nonFlatSchema

end Silmaril.Formats.Parquet.Footer.NestedLeaf
