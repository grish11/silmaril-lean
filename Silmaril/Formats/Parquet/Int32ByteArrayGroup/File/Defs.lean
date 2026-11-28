module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Defs

/-! A bounded typed source over every footer group of one checked INT32 and
BYTE_ARRAY projection. -/

public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.File

open Silmaril.Relational

structure Limits where
  group : Int32ByteArrayGroup.Limits := {}
  maxFileRows : Nat := 1024 * 1024

inductive Error where
  | openFailure (reason : Int32ByteArrayGroup.Error)
  | fileRowLimit (maximum actual : Nat)
  | groupFailure (index : Nat) (reason : Int32ByteArrayGroup.Error)
  deriving DecidableEq, Repr

inductive Kind where
  | int32 (layout : FlatColumn.Layout)
  | byteArray (layout : FlatColumn.Layout)
  deriving DecidableEq, Repr

abbrev Value : Kind → Type
  | .int32 _ => Int32
  | .byteArray _ => Bytes

@[expose] def schema (int32 byteArray : Field) : Scan.Schema String Kind :=
  ⟨2, fun i => if i.val = 0 then (int32.name, .int32 int32.layout)
    else (byteArray.name, .byteArray byteArray.layout)⟩

/-- A pair contributes one typed row at its original position. -/
@[expose] def rows (int32 byteArray : Field) (pairs : List Int32ByteArrayGroup.Row) :
    Reader.RowGroup (schema int32 byteArray) Value :=
  pairs.map fun pair i => by
    change Option (Value (if i.val = 0 then (int32.name, Kind.int32 int32.layout)
      else (byteArray.name, Kind.byteArray byteArray.layout)).2)
    split
    · exact pair.1
    · exact pair.2

/-- The checked projection retains the one snapshot and the file admission cap. -/
structure Checked (limits : Limits) (int32 byteArray : Field) where
  private mk ::
  projection : Int32ByteArrayGroup.Checked int32 byteArray
  rowCap : projection.snapshot.metadata.numRows.toNat ≤ limits.maxFileRows

/-- Check the file and bind both fields once. The footer validator has already
equated the file count with the sum of its nonnegative group counts. -/
def openFile (limits : Limits) (input : Bytes) (int32 byteArray : Field) :
    Except Error (Checked limits int32 byteArray) := do
  let projection ← (Int32ByteArrayGroup.openFile limits.group input int32 byteArray).mapError .openFailure
  let count := projection.snapshot.metadata.numRows.toNat
  if admitted : count ≤ limits.maxFileRows then pure ⟨projection, admitted⟩
  else throw (.fileRowLimit limits.maxFileRows count)

variable {limits : Limits} {int32 byteArray : Field}

/-- Read each checked footer ordinal once. The original selected error stays
inside the enclosing indexed group error. -/
@[expose] def Checked.source (checked : Checked limits int32 byteArray) :
    Reader.Source Nat (schema int32 byteArray) Value Error :=
  ⟨List.range checked.projection.snapshot.groupCount,
    fun index => (checked.projection.readGroup limits.group index).map (rows int32 byteArray) |>.mapError
      (.groupFailure index),
    fun _ => .ok ()⟩

/-- Open the typed source. Callers choose how to consume its ordered batches. -/
@[expose] def openSource (limits : Limits) (input : Bytes) (int32 byteArray : Field) :
    Reader.OpenResult Nat String Value Error :=
  (openFile limits input int32 byteArray).map fun checked => ⟨schema int32 byteArray, checked.source⟩

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.File
