module

public import Silmaril.Formats.Hive.Manifest.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Defs

/-!
# Checked Hive manifests over a selected Parquet INT32 and BYTE_ARRAY pair

The source opens the file once and binds the selected pair. Check the names of
all flat physical leaves against the virtual partition names before reading
groups. Use the existing strict manifest scan at the selected pair schema.
-/

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema extendRow)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

namespace Int32ByteArray

inductive Error (Failure : Type) where
  | lookup (reason : Failure)
  | parquet (reason : Int32ByteArrayGroup.File.Error)
  | reservedPartition (name : String)
  deriving DecidableEq, Repr

variable {Failure : Type} {int32 byteArray : Field} {limits : Int32ByteArrayGroup.File.Limits}

private def openChecked (limits : Int32ByteArrayGroup.File.Limits) (int32 byteArray : Field)
    (partitions : PartitionSchema Kind) (lookup : String → Except Failure Bytes)
    (path : String) : Except (Error Failure) (Int32ByteArrayGroup.File.Checked limits int32 byteArray) := do
  let bytes ← (lookup path).mapError Error.lookup
  let checked ← (Int32ByteArrayGroup.File.openFile limits bytes int32 byteArray).mapError Error.parquet
  let leaves := checked.projection.snapshot.metadata.schema.drop 1
  if let some collision := leaves.find? (fun leaf => partitions.keys.contains leaf.name) then
    throw (.reservedPartition collision.name)
  pure checked

private def source (checked : Int32ByteArrayGroup.File.Checked limits int32 byteArray) :
    Reader.Source Nat (Int32ByteArrayGroup.File.schema int32 byteArray) Value (Error Failure) :=
  let physical := checked.source
  ⟨physical.groups, fun group => (physical.readGroup group).mapError Error.parquet,
    fun remaining => (physical.close remaining).mapError Error.parquet⟩

end Int32ByteArray

variable {Failure : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

/-- Use the original literal path, then check the Parquet open and pair binding.
Reject the first reserved partition name in physical leaf order, including
unselected leaves. On success, read the selected pair through file EOS. -/
def int32ByteArraySnapshotOpener (limits : Int32ByteArrayGroup.File.Limits) (int32 byteArray : Field)
    (partitions : PartitionSchema Kind) (lookup : String → Except Failure Bytes) :
    Opener Nat (Int32ByteArrayGroup.File.schema int32 byteArray) Value (Int32ByteArray.Error Failure) := fun path =>
  (Int32ByteArray.openChecked limits int32 byteArray partitions lookup path).map fun checked =>
    let source := Int32ByteArray.source checked
    ⟨source, source.groups.length + 1⟩

private def denoteInt32ByteArrayFile (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (file : File partitions Value) :
    Events.Trace projection.schema Value (FileError (Int32ByteArray.Error Failure)) :=
  let path := file.path.declared
  match Int32ByteArray.openChecked limits int32 byteArray partitions lookup path with
  | .error reason => ⟨[], .readError (.open path reason)⟩
  | .ok checked =>
    let source := Int32ByteArray.source checked
    let groups := Reader.denoteGroups source.readGroup source.groups
    let batches := if (keep file.cells).getD false then
      groups.1.map fun rows =>
        AlignedColumns.ofRows (projection.project (rows.map fun row => extendRow row file.cells))
      else []
    let termination := match groups.2 with
      | .eos => .eos
      | .closed => .closed
      | .readError reason => .readError (.source path reason)
      | .closeError reason => .closeError (.source path reason)
    ⟨batches, termination⟩

/-- Independently denote each checked file's groups, construct selected
batches from the typed rows, and advance only at file EOS. -/
def denoteInt32ByteArraySnapshots (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) :
    List (File partitions Value) → Events.Trace projection.schema Value (FileError (Int32ByteArray.Error Failure))
  | [] => ⟨[], .eos⟩
  | file :: rest =>
    let current := denoteInt32ByteArrayFile limits lookup projection keep file
    match current.termination with
    | .eos =>
      let tail := denoteInt32ByteArraySnapshots limits lookup projection keep rest
      ⟨current.batches ++ tail.batches, tail.termination⟩
    | _ => current

end Silmaril.Formats.Hive.Manifest
