module

public import Silmaril.Formats.Parquet.FlatScan.Scalar.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.File.Defs

/-! One row group projected to a named PLAIN INT32 and a named PLAIN
BYTE_ARRAY leaf, using one checked plaintext snapshot. -/

public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup

structure Field where
  name : String
  layout : FlatColumn.Layout
  deriving DecidableEq, Repr

inductive Selection where
  | int32
  | byteArray
  deriving DecidableEq, Repr

structure Limits where
  snapshot : Snapshot.Limits := {}
  column : FlatColumn.Limits := {}
  maxFileBytes : Nat := 256 * 1024 * 1024
  maxValueBytes : Nat := 16 * 1024 * 1024

private def Limits.byteArray (limits : Limits) : Plain.ByteArray.File.Limits :=
  { column := limits.column, maxValueBytes := limits.maxValueBytes }

inductive Error where
  | fileByteLimit (maximum actual : Nat)
  | duplicateName (name : String)
  | snapshot (reason : Snapshot.Error Unit)
  | bind (selection : Selection) (reason : FlatColumn.BindError)
  | int32 (reason : FlatColumn.Error FlatScan.AdapterError)
  | byteArray (reason : FlatColumn.Error Plain.ByteArray.File.PageError)
  | alignment (group int32Count byteArrayCount : Nat)
  deriving DecidableEq, Repr

abbrev Row := Option Int32 × Option Bytes

def decodeInt32 (limits : Limits) (layout : FlatColumn.Layout) :
    FlatColumn.DecodePage Int32 FlatScan.AdapterError :=
  let flatLayout := match layout with
    | .required => FlatPage.Layout.required
    | .optional => FlatPage.Layout.optional
  fun leaf _ header body =>
    FlatScan.decodeInt32Page limits.byteArray.scalar ⟨leaf.name, flatLayout⟩ header body

def decodeByteArray (limits : Limits) (layout : FlatColumn.Layout) :
    FlatColumn.DecodePage Bytes Plain.ByteArray.File.PageError :=
  Plain.ByteArray.File.decodePage limits.byteArray layout

structure Checked (int32 byteArray : Field) where
  private mk ::
  snapshot : Snapshot.Checked
  int32Binding : FlatColumn.Binding snapshot ⟨int32.name, .int32, int32.layout⟩
  byteArrayBinding : FlatColumn.Binding snapshot ⟨byteArray.name, .byteArray, byteArray.layout⟩

/-- Check the file once and bind the two exact leaves before reading any page. -/
def openFile (limits : Limits) (source : Bytes) (int32 byteArray : Field) :
    Except Error (Checked int32 byteArray) :=
  if limits.maxFileBytes < source.length then .error (.fileByteLimit limits.maxFileBytes source.length)
  else if int32.name = byteArray.name then .error (.duplicateName int32.name)
  else do
    let snapshot ← (Snapshot.check limits.snapshot source).mapError .snapshot
    let left ← (FlatColumn.bindColumn snapshot ⟨int32.name, .int32, int32.layout⟩).mapError (.bind .int32)
    let right ← (FlatColumn.bindColumn snapshot ⟨byteArray.name, .byteArray, byteArray.layout⟩).mapError
      (.bind .byteArray)
    pure ⟨snapshot, left, right⟩

variable {int32 byteArray : Field}

/-- Read a selected column with the original typed group, column and page errors. -/
@[expose] def Checked.readInt32 (checked : Checked int32 byteArray) (limits : Limits) (index : Nat) :
    Except (FlatColumn.Error FlatScan.AdapterError) (List (Option Int32)) :=
  FlatColumn.readColumn checked.int32Binding limits.column Plain.ByteArray.File.policy
    (decodeInt32 limits int32.layout) index

@[expose] def Checked.readByteArray (checked : Checked int32 byteArray) (limits : Limits) (index : Nat) :
    Except (FlatColumn.Error Plain.ByteArray.File.PageError) (List (Option Bytes)) :=
  FlatColumn.readColumn checked.byteArrayBinding limits.column Plain.ByteArray.File.policy
    (decodeByteArray limits byteArray.layout) index

/-- Read INT32 first, then BYTE_ARRAY. Zip only after checking equal lengths.
Both input lists have already been checked against the same footer group. -/
@[expose] def Checked.readGroup (checked : Checked int32 byteArray) (limits : Limits)
    (index : Nat) : Except Error (List Row) :=
  match checked.readInt32 limits index with
  | .error reason => .error (.int32 reason)
  | .ok integers =>
    match checked.readByteArray limits index with
    | .error reason => .error (.byteArray reason)
    | .ok bytes =>
      if integers.length = bytes.length then .ok (integers.zip bytes)
      else .error (.alignment index integers.length bytes.length)

/-- Open and read one group by its original zero-based footer ordinal. -/
def readFileRowGroup (limits : Limits) (source : Bytes) (int32 byteArray : Field) (index : Nat) :
    Except Error (List Row) := do
  let checked ← openFile limits source int32 byteArray
  checked.readGroup limits index

/-- Both selected columns witness their original framed chunks in the same
group. Pairing consumes both complete slot lists in position order. -/
@[expose] def GroupWire (checked : Checked int32 byteArray) (limits : Limits)
    (index : Nat) (rows : List Row) : Prop :=
  ∃ (group : Footer.RowGroup) (integers : List (Option Int32)) (bytes : List (Option Bytes)),
    FlatColumn.ColumnWire checked.int32Binding limits.column (decodeInt32 limits int32.layout) index group integers ∧
    FlatColumn.ColumnWire checked.byteArrayBinding limits.column (decodeByteArray limits byteArray.layout) index group bytes ∧
    checked.readInt32 limits index = .ok integers ∧ checked.readByteArray limits index = .ok bytes ∧
    integers.length = bytes.length ∧ rows.length = group.numRows.toNat ∧
    rows = integers.zip bytes ∧ rows.unzip = (integers, bytes)

end Silmaril.Formats.Parquet.Int32ByteArrayGroup
