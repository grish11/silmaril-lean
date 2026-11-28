module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Defs

/-! A bounded typed source for the fixed-tag-6 group projection. -/

public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File

open Silmaril.Relational

structure Limits where
  group : DeltaLength.Limits := {}
  maxFileRows : Nat := ({} : Int32ByteArrayGroup.File.Limits).maxFileRows

/-- Use the existing file admission with the same base group limits as the
delta reads. -/
@[expose] def Limits.admission (limits : Limits) : Int32ByteArrayGroup.File.Limits :=
  ⟨limits.group.group, limits.maxFileRows⟩

inductive Error where
  | openFailure (reason : Int32ByteArrayGroup.File.Error)
  | groupFailure (index : Nat) (reason : DeltaLength.Error)
  deriving DecidableEq, Repr

abbrev Kind := Int32ByteArrayGroup.File.Kind
abbrev Value := Int32ByteArrayGroup.File.Value

@[expose] def schema (int32Name byteArrayName : String) : Scan.Schema String Kind :=
  Int32ByteArrayGroup.File.schema ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩

@[expose] def rows (int32Name byteArrayName : String) (pairs : List Int32ByteArrayGroup.Row) :
    Reader.RowGroup (schema int32Name byteArrayName) Value :=
  Int32ByteArrayGroup.File.rows ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩ pairs

abbrev Checked (limits : Limits) (int32Name byteArrayName : String) :=
  Int32ByteArrayGroup.File.Checked limits.admission ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩

/-- Check and bind the snapshot once, with the total row cap before any group
callback. Page decoding begins only when the cursor is consumed. -/
@[expose] def openFile (limits : Limits) (input : Bytes) (int32Name byteArrayName : String) :
    Except Error (Checked limits int32Name byteArrayName) :=
  (Int32ByteArrayGroup.File.openFile limits.admission input ⟨int32Name, .required⟩
    ⟨byteArrayName, .optional⟩).mapError .openFailure

variable {limits : Limits} {int32Name byteArrayName : String}

/-- The dense cursor keeps the original footer ordinals, including empty
groups. Every call uses the fixed-tag-6 group reader on the retained snapshot. -/
@[expose] def source (checked : Checked limits int32Name byteArrayName) :
    Reader.Source Nat (schema int32Name byteArrayName) Value Error :=
  ⟨List.range checked.projection.snapshot.groupCount,
    fun index => (DeltaLength.readGroup checked.projection limits.group index).map
      (rows int32Name byteArrayName) |>.mapError (.groupFailure index),
    fun _ => .ok ()⟩

@[expose] def openSource (limits : Limits) (input : Bytes) (int32Name byteArrayName : String) :
    Reader.OpenResult Nat String Value Error :=
  (openFile limits input int32Name byteArrayName).map fun checked => ⟨schema int32Name byteArrayName, source checked⟩

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File
