module

public import Silmaril.Formats.Parquet.ByteStreamSplitPage.Defs
public import Silmaril.Formats.Parquet.FlatColumn.Defs
public import Silmaril.Formats.Parquet.RleBooleanPage.Defs

/-! A two-column typed reader with independent BOOLEAN and FLOAT page
segmentation. FLOAT values are the original IEEE-754 words. -/

public section

namespace Silmaril.Formats.Parquet.MixedBooleanFloat

open Silmaril.Relational Silmaril.Formats.Arrow

inductive Kind where
  | boolean
  | floatBits
  deriving DecidableEq, Repr

abbrev Value : Kind → Type
  | .boolean => Bool
  | .floatBits => UInt32

@[expose] def schema (booleanName floatName : String) : Scan.Schema String Kind :=
  ⟨2, fun column => if column.val = 0 then (booleanName, .boolean) else (floatName, .floatBits)⟩

@[expose] def row {booleanName floatName : String} (boolean : Option Bool) (bits : Option UInt32) :
    Scan.Row (schema booleanName floatName) Value :=
  fun column => by
    change Option (Value (if column.val = 0 then (booleanName, Kind.boolean) else (floatName, Kind.floatBits)).2)
    split
    · exact boolean
    · exact bits

structure Limits where
  snapshot : Snapshot.Limits := {}
  column : FlatColumn.Limits := {}
  maxFileBytes : Nat := 256 * 1024 * 1024

private def scalarLimits (limits : FlatColumn.Limits) : ScalarPage.Limits :=
  ⟨limits.maxPageBytes, limits.maxPageBytes, ⟨limits.maxRows, limits.maxPageBytes⟩, 0⟩

inductive DecodeError where
  | nonDataPage
  | boolean (reason : RleBooleanPage.Error)
  | float (reason : ByteStreamSplitPage.Error)
  | unexpectedKind
  deriving DecidableEq, Repr

@[expose] def booleanPolicy : FlatColumn.Policy := ⟨3, .v1AndV2⟩

@[expose] def floatPolicy : FlatColumn.Policy := ⟨9, .v1AndV2⟩

def decodeBoolean (limits : FlatColumn.Limits) : FlatColumn.DecodePage Bool DecodeError :=
  fun _ metadata header body => do
    let some params := FlatColumn.pageParameters .optional metadata.codec header | throw .nonDataPage
    (RleBooleanPage.decode metadata.physicalType params
      ⟨scalarLimits limits, ⟨limits.maxRows, limits.maxPageBytes⟩⟩ body).mapError .boolean

def decodeFloat (limits : FlatColumn.Limits) : FlatColumn.DecodePage UInt32 DecodeError :=
  fun leaf metadata header body => do
    let some params := FlatColumn.pageParameters .optional metadata.codec header | throw .nonDataPage
    let ⟨.floatBits, slots⟩ ← (ByteStreamSplitPage.decode leaf metadata.physicalType params
      ⟨scalarLimits limits, ⟨limits.maxRows, limits.maxPageBytes, 4⟩⟩ body).mapError .float
      | throw .unexpectedKind
    pure slots

inductive Failure where
  | fileByteLimit
  | schemaArity
  | bind (column : Nat) (reason : FlatColumn.BindError)
  | columnOrder
  | scan (reason : FlatColumn.Error DecodeError)
  | alignment (group expected booleanCount floatCount : Nat)
  deriving DecidableEq, Repr

/-- A mixed profile bound once to exactly two schema leaves in the same snapshot. -/
structure Checked (booleanName floatName : String) where
  private mk ::
  snapshot : Snapshot.Checked
  boolean : FlatColumn.Binding snapshot ⟨booleanName, .boolean, .optional⟩
  float : FlatColumn.Binding snapshot ⟨floatName, .float, .optional⟩
  booleanOrder : boolean.columnOrdinal = 0
  floatOrder : float.columnOrdinal = 1

def openFile (limits : Limits) (source : Bytes) (booleanName floatName : String) :
    Except (Snapshot.Error Failure) (Checked booleanName floatName) :=
  if limits.maxFileBytes < source.length then .error (.input .fileByteLimit)
  else do
    let snapshot ← Snapshot.check limits.snapshot source
    if snapshot.metadata.schema.length != 3 then .error (.schema .schemaArity)
    else do
      let boolean ← (FlatColumn.bindColumn snapshot ⟨booleanName, .boolean, .optional⟩).mapError (.schema ∘ .bind 0)
      let float ← (FlatColumn.bindColumn snapshot ⟨floatName, .float, .optional⟩).mapError (.schema ∘ .bind 1)
      if order : boolean.columnOrdinal = 0 ∧ float.columnOrdinal = 1 then
        pure ⟨snapshot, boolean, float, order.1, order.2⟩
      else throw (.schema .columnOrder)

/-- The row index ranges over the common length. The two arrays may come
from any respective page partition and each position is read exactly once. -/
@[expose] def assemble {booleanName floatName : String} {n : Nat}
    (booleans : Vector (Option Bool) n) (floats : Vector (Option UInt32) n) :
    Reader.RowGroup (schema booleanName floatName) Value :=
  List.ofFn fun i => row (booleans.get i) (floats.get i)

private def align {booleanName floatName : String} (index rows : Nat)
    (booleans : List (Option Bool)) (floats : List (Option UInt32)) :
    Except Failure (Reader.RowGroup (schema booleanName floatName) Value) :=
  let boolArray := booleans.toArray
  let floatArray := floats.toArray
  if lengths : boolArray.size = rows ∧ floatArray.size = rows then
    .ok (assemble ⟨boolArray, lengths.1⟩ ⟨floatArray, lengths.2⟩)
  else .error (.alignment index rows boolArray.size floatArray.size)

def Checked.readGroup {booleanName floatName : String} (checked : Checked booleanName floatName)
    (limits : FlatColumn.Limits) (index : Nat) :
    Except Failure (Reader.RowGroup (schema booleanName floatName) Value) := do
  let some group := checked.snapshot.groupAt index | throw (.scan (.groupIndex index))
  let booleans ← (FlatColumn.readColumn checked.boolean limits booleanPolicy (decodeBoolean limits) index).mapError .scan
  let floats ← (FlatColumn.readColumn checked.float limits floatPolicy (decodeFloat limits) index).mapError .scan
  align index group.numRows.toNat booleans floats

/-- Both ordered column results refer to the same footer group. Every
row takes the two slots at its position in the flattened column streams. -/
@[expose] def Checked.GroupWire {booleanName floatName : String} (checked : Checked booleanName floatName)
    (limits : FlatColumn.Limits) (index : Nat)
    (rows : Reader.RowGroup (schema booleanName floatName) Value) : Prop :=
  ∃ (group : Footer.RowGroup) (booleans : List (Option Bool)) (floats : List (Option UInt32)),
    FlatColumn.ColumnWire checked.boolean limits (decodeBoolean limits) index group booleans ∧
    FlatColumn.ColumnWire checked.float limits (decodeFloat limits) index group floats ∧
    rows.length = group.numRows.toNat ∧
    ∀ i, i < group.numRows.toNat → rows[i]? = some (row (booleans[i]?.join) (floats[i]?.join))

/-- Publish a group only after both columns succeed. Snapshot supplies the
indexed first-error boundary and publishes preceding complete batches. -/
def readAll (limits : Limits) (source : Bytes) (booleanName floatName : String) :
    Events.EventStream String Value (Snapshot.Error Failure) :=
  match openFile limits source booleanName floatName with
  | .error reason => .error reason
  | .ok checked => checked.snapshot.readAll (schema := schema booleanName floatName)
      (fun _ index _ => checked.readGroup limits.column index)

end Silmaril.Formats.Parquet.MixedBooleanFloat
