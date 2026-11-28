module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Defs

/-! Checked partition cells for the paired INT32 and opaque BYTE_ARRAY manifest. -/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest.Int32ByteArray.Ingress

open Silmaril.Formats.Parquet
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (PartitionSchema)

inductive CastError where
  | invalidInt32 (text : String)
  | int32OutOfRange (value : Int)
  deriving BEq, Repr

/-- Parse decimal digits with an optional leading minus. -/
def parseDecimal (text : String) : Option Int :=
  let digits := match text.toList with
    | '-' :: rest => rest
    | rest => rest
  if digits.all Char.isDigit then text.toInt? else none

/-- Check signed INT32 before constructing the value. A BYTE_ARRAY path
constant is the UTF-8 of the decoded text, including the empty string. -/
def convert : TypedPartitions.Convert Value CastError := fun field text =>
  match field.kind with
  | .int32 _ =>
    match parseDecimal text with
    | none => .error (.invalidInt32 text)
    | some value =>
      if bounds : Int32.minValue.toInt ≤ value ∧ value ≤ Int32.maxValue.toInt then
        .ok (Int32.ofIntLE value bounds.1 bounds.2)
      else .error (.int32OutOfRange value)
  | .byteArray _ => .ok ⟨text.toUTF8⟩

inductive Error where
  | prepare (reason : PrepareError CastError)
  | requiredNull (path field : String)
  deriving BEq, Repr

def layout : Kind → FlatColumn.Layout
  | .int32 layout | .byteArray layout => layout

variable {schema : PartitionSchema Kind}

def firstRequiredNull (file : File schema Value) : Option (Fin schema.toScan.width) :=
  (List.finRange schema.toScan.width).find? fun i =>
    decide (layout (schema.toScan.kind i).2 = .required) && (file.cells i).isNone

/-- Run the shared path and binding checks first. Then reject a null required
cell, whether it came from the marker or the field's missing-as-null policy. -/
def preparePath (schema : PartitionSchema Kind) (options : PartitionPath.Options)
    (path : String) : Except Error (File schema Value) :=
  match Manifest.prepareFile schema options convert path with
  | .error reason => .error (.prepare reason)
  | .ok file =>
    match firstRequiredNull file with
    | some i => .error (.requiredNull path (schema.toScan.kind i).1)
    | none => .ok file

/-- Check names even for an empty list, then prepare each literal occurrence
in order. Full physical-leaf collision checks belong to the paired opener. -/
def preparePaths (int32 byteArray : Field) (schema : PartitionSchema Kind)
    (options : PartitionPath.Options) (paths : List String) : Except Error (List (File schema Value)) :=
  match TypedPartitions.checkSchema (Int32ByteArrayGroup.File.schema int32 byteArray) schema with
  | .error reason => .error (.prepare (.schema reason))
  | .ok () => paths.mapM (preparePath schema options)

end Silmaril.Formats.Hive.Manifest.Int32ByteArray.Ingress
