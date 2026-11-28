module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs
import Silmaril.Formats.Hive.Manifest.Thms
import Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress

public section

namespace Silmaril.Formats.Hive.Manifest.Int32ByteArray.Ingress

open Silmaril.Formats.Parquet
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (PartitionSchema)

variable {schema : PartitionSchema Kind} {options : PartitionPath.Options}

/-- The parsed mathematical integer must equal the signed output. -/
theorem convert_int32_ok_iff (name : String) (nullability : FlatColumn.Layout)
    (missing : TypedPartitions.Missing) (text : String) (value : Int32) :
    convert ⟨name, .int32 nullability, missing⟩ text = .ok value ↔ parseDecimal text = some value.toInt :=
  Proofs.Formats.Hive.Manifest.Int32ByteArray.Ingress.convert_int32_ok_iff
    name nullability missing text value

theorem convert_byteArray (name : String) (nullability : FlatColumn.Layout)
    (missing : TypedPartitions.Missing) (text : String) :
    convert ⟨name, .byteArray nullability, missing⟩ text = .ok ⟨text.toUTF8⟩ := rfl

/-- A checked occurrence is the same binding in declared field order, with
every required cell present. -/
theorem preparePath_ok_iff {path : String} {file : File schema Value} :
    preparePath schema options path = .ok file ↔
      Manifest.prepareFile schema options convert path = .ok file ∧
      ∀ i, layout (schema.toScan.kind i).2 = .required → (file.cells i).isSome = true :=
  Proofs.Formats.Hive.Manifest.Int32ByteArray.Ingress.preparePath_ok_iff

/-- Success preserves the entire ordered generic binding, refining its cell
policy with a non-null check for required fields. -/
theorem preparePaths_ok_iff (int32 byteArray : Field)
    {paths : List String} {files : List (File schema Value)} :
    preparePaths int32 byteArray schema options paths = .ok files ↔
      Manifest.prepare (Int32ByteArrayGroup.File.schema int32 byteArray) schema options convert paths =
        .ok files ∧
      ∀ file ∈ files, ∀ i, layout (schema.toScan.kind i).2 = .required → (file.cells i).isSome = true :=
  Proofs.Formats.Hive.Manifest.Int32ByteArray.Ingress.preparePaths_ok_iff int32 byteArray

/-- The checked opener receives the original path spellings, with repeats. -/
theorem preparePaths_preserves_paths (int32 byteArray : Field)
    {paths : List String} {files : List (File schema Value)}
    (prepared : preparePaths int32 byteArray schema options paths = .ok files) :
    files.map (fun file => file.path.declared) = paths :=
  Manifest.prepare_preserves_paths options convert ((preparePaths_ok_iff int32 byteArray).mp prepared).1

end Silmaril.Formats.Hive.Manifest.Int32ByteArray.Ingress
