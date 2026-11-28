module

public import Silmaril.Formats.Parquet.ColumnIndex.Signed.Defs

/-! Reference observations for the signed diagnostic before sharing footer
selection. This module is used only by its compatibility theorem header. -/

public section

namespace Silmaril.Formats.Parquet.ColumnIndex.Signed.Compatibility

open ThriftCompact
open Traversal (Field Reader)

private def readStruct (reader : Reader) (start : Nat) : Except OrderError (List Field × Nat) :=
  (Traversal.readStruct reader start).mapError .compact

private def field? (fields : List Field) (id : Int) : Except OrderError (Option Field) :=
  match fields.filter (·.id == id) with
  | [] => .ok none
  | [field] => .ok (some field)
  | _ => .error .footerShape

private def structList (reader : Reader) (field : Field) : Except OrderError (List (List Field)) := do
  if field.type ≠ .payload .list then throw .footerShape
  let (result, stop) ← Traversal.readList reader OrderError.compact .struct (readStruct reader) field.start
  if stop ≠ field.stop then throw .footerShape
  pure result

/-- Read the original raw leaf and column-order union at their respective
ordinals in the exact checked footer slice. -/
def readOrderFields (limits : Footer.Limits) (snapshot : Snapshot.Checked)
    {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) : Except OrderError OrderFields := do
  if snapshot.footer.stop - snapshot.footer.start > limits.maxFooterBytes then throw .footerByteLimit
  let source := Footer.fileBytes snapshot.bytes snapshot.footer.start snapshot.footer.stop
  let reader : Reader := ⟨source, limits.compact, limits.varintMode⟩
  let (fields, stop) ← readStruct reader 0
  if stop ≠ source.length then throw .footerShape
  let some schemaField ← field? fields 2 | throw .footerShape
  let schema ← structList reader schemaField
  if schema.length ≠ snapshot.metadata.schema.length then throw .footerShape
  let some leaf := schema[binding.leafOrdinal]? | throw .footerShape
  let some order ← field? fields 7 | throw .missingOrder
  let orders ← structList reader order
  if orders.length + 1 ≠ schema.length then throw .footerShape
  let some selected := orders[binding.columnOrdinal]? | throw .footerShape
  pure ⟨reader, leaf, selected⟩

def checkOrder (limits : Footer.Limits) (snapshot : Snapshot.Checked)
    {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) : Except OrderError Unit :=
  readOrderFields limits snapshot binding >>= checkOrderFields

def diagnose (limits : Limits) {snapshot : Snapshot.Checked} {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) (group : Nat) (slots : Slots) :
    Except Error (Option (List (Option Bounds))) := do
  let index ← (ColumnIndex.validate limits.indexFraming snapshot group binding.columnOrdinal).mapError .index
  let some present := index | return none
  (Compatibility.checkOrder limits.index.offsetIndex.snapshot.footer snapshot binding).mapError .order
  some <$> check present (splitPages present.offsetIndex.pages slots)

end Silmaril.Formats.Parquet.ColumnIndex.Signed.Compatibility
