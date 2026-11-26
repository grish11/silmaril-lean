module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Defs

/-! Pair a required PLAIN INT32 leaf and an optional legacy-fallback BYTE_ARRAY leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy

open Silmaril.Relational Silmaril.Formats.Arrow

structure Limits where
  file : Int32ByteArrayGroup.File.Limits := {}
  maxDictionaryEntries : Nat := 1024 * 1024
  maxDictionaryBytes : Nat := 4 * 1024 * 1024

def Limits.binary (limits : Limits) : ByteArrayFallback.Limits where
  file := {
    snapshot := limits.file.group.snapshot
    column := limits.file.group.column
    maxFileBytes := limits.file.group.maxFileBytes
    maxFileRows := limits.file.maxFileRows
    maxValueBytes := limits.file.group.maxValueBytes
  }
  maxDictionaryEntries := limits.maxDictionaryEntries
  maxDictionaryBytes := limits.maxDictionaryBytes

inductive Error where
  | openFailure (cause : Int32ByteArrayGroup.File.Error)
  | int32 (cause : FlatColumn.Error FlatScan.AdapterError)
  | byteArray (cause : ByteArrayFallback.Error)
  | alignment (group integers bytes : Nat)
  deriving DecidableEq, Repr

abbrev Kind := Int32ByteArrayGroup.File.Kind
abbrev Value := Int32ByteArrayGroup.File.Value

def schema (int32Name byteArrayName : String) : Scan.Schema String Kind :=
  Int32ByteArrayGroup.File.schema ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩

def rows (int32Name byteArrayName : String) (values : List Int32ByteArrayGroup.Row) :
    Reader.RowGroup (schema int32Name byteArrayName) Value :=
  Int32ByteArrayGroup.File.rows ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩ values

abbrev Checked (limits : Limits) (int32Name byteArrayName : String) :=
  Int32ByteArrayGroup.File.Checked limits.file ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩

/-- Bind both exact leaves and apply the file cap before any selected group read. -/
def openFile (limits : Limits) (input : Bytes) (int32Name byteArrayName : String) :
    Except Error (Checked limits int32Name byteArrayName) :=
  (Int32ByteArrayGroup.File.openFile limits.file input ⟨int32Name, .required⟩
    ⟨byteArrayName, .optional⟩).mapError .openFailure

def policy : FlatColumn.Policy := ⟨0, .legacyV1Required⟩

/-- A checked required flat V1 frame has no level bytes. Its exact body is
the signed PLAIN words. The column walk admits the original header first. -/
def decodeInt32 : FlatColumn.DecodePage Int32 FlatScan.AdapterError :=
  fun _ _ header body => do
    let .dataV1 data := header.kind | throw .unsupportedKind
    let values ← (Plain.decodeInt32 data.numValues body).mapError (.scalar ∘ .plain)
    return values.map some

variable {limits : Limits} {int32Name byteArrayName : String}

def readInts (checked : Checked limits int32Name byteArrayName) (index : Nat) :
    Except (FlatColumn.Error FlatScan.AdapterError) (List (Option Int32)) :=
  FlatColumn.readColumn checked.projection.int32Binding limits.file.group.column policy decodeInt32 index

def readBytes (checked : Checked limits int32Name byteArrayName) (index : Nat) :
    Except ByteArrayFallback.Error (List (Option Bytes)) :=
  ByteArrayFallback.readBoundGroupFor .plainDictionaryV1 checked.projection.byteArrayBinding limits.binary index

/-- Read INT32 first. Publish paired slots only after both columns succeed. -/
def readGroup (checked : Checked limits int32Name byteArrayName) (index : Nat) :
    Except Error (List Int32ByteArrayGroup.Row) := do
  let integers ← (readInts checked index).mapError .int32
  let bytes ← (readBytes checked index).mapError .byteArray
  if integers.length = bytes.length then pure (integers.zip bytes)
  else throw (.alignment index integers.length bytes.length)

def GroupWire (checked : Checked limits int32Name byteArrayName) (index : Nat)
    (pairs : List Int32ByteArrayGroup.Row) : Prop :=
  ∃ (group : Footer.RowGroup) (integers : List (Option Int32)) (bytes : List (Option Bytes)),
    FlatColumn.ColumnWire checked.projection.int32Binding limits.file.group.column decodeInt32 index group integers ∧
    ByteArrayFallback.BoundGroupWireFor .plainDictionaryV1 checked.projection.byteArrayBinding
      limits.binary index group bytes ∧
    pairs.length = group.numRows.toNat ∧ pairs = integers.zip bytes ∧ pairs.unzip = (integers, bytes)

def rowsAt (checked : Checked limits int32Name byteArrayName) (index : Nat) :
    Except Error (Reader.RowGroup (schema int32Name byteArrayName) Value) :=
  (readGroup checked index).map (rows int32Name byteArrayName)

def source (checked : Checked limits int32Name byteArrayName) :
    Reader.Source Nat (schema int32Name byteArrayName) Value Error :=
  ⟨List.range checked.projection.snapshot.groupCount, rowsAt checked, fun _ => .ok ()⟩

def openSource (limits : Limits) (input : Bytes) (int32Name byteArrayName : String) :
    Reader.OpenResult Nat String Value Error :=
  (openFile limits input int32Name byteArrayName).map fun checked =>
    ⟨schema int32Name byteArrayName, source checked⟩

def readAll (limits : Limits) (input : Bytes) (int32Name byteArrayName : String) :
    Events.EventStream String Value Error :=
  Reader.readAll (openSource limits input int32Name byteArrayName)

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy
