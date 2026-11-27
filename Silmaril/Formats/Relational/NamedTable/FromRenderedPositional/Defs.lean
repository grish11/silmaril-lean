module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedPositional.Defs
public import Silmaril.Formats.Relational.NamedTable.Defs

/-! Atomic named insertion from a bounded rendered positional Parquet scan. -/

@[expose] public section

namespace Silmaril.Formats.Relational.NamedTable.FromRenderedPositional

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Hive Silmaril.Formats.Parquet
open Manifest (FileError)
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

inductive SourceError (Admission Failure : Type) where
  | admission (reason : Manifest.Inventory.Error Admission)
  | runtime (reason : FileError (Manifest.Int32ByteArray.Error Failure))

abbrev Database (Name : Type*) := NamedTable.Packed Name String Value

abbrev ScanResult (schema : Scan.Schema String Kind) (Admission Failure : Type) :=
  Except (Manifest.Inventory.Error Admission)
    (Events.Trace schema Value (FileError (Manifest.Int32ByteArray.Error Failure)))

variable {Name : Type*} {Admission Failure : Type} {schema : Scan.Schema String Kind}

/-- Admission failure has no opened schema. Otherwise the projected batches
and terminal outcome are carried to the shared Arrow import. -/
def toEventStream (result : ScanResult schema Admission Failure) :
    Events.EventStream String Value (SourceError Admission Failure) :=
  match result with
  | .error reason => .error (.admission reason)
  | .ok trace =>
    let termination := match trace.termination with
      | .eos => .eos
      | .closed => .closed
      | .readError reason => .readError (.runtime reason)
      | .closeError reason => .closeError (.runtime reason)
    .ok ⟨schema, ⟨trace.batches, termination⟩⟩

/-- Use the exact projected schema and retain the named import's vacancy and
EOS policy. Only a complete import returns an updated database. -/
def importResult [DecidableEq Name] (db : Database Name) (name : Name)
    (result : ScanResult schema Admission Failure) :
    Except (NamedTable.ImportError (SourceError Admission Failure)) (Database Name) :=
  NamedTable.importArrow db name schema (toEventStream result)

variable {int32 byteArray : Field} {partitions : PartitionSchema Kind}

/-- Scan the supplied listing at the requested projection and action budget,
then import its exhausted result under the exact projected schema. -/
def importScan [DecidableEq Name] (db : Database Name) (name : Name)
    (admission : Manifest.Inventory.Limits) (maxDirectoryBytes : Nat) (keys : List String)
    (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (convert : Convert Value Admission) (listing : List String) (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) :
    Except (NamedTable.ImportError (SourceError Admission Failure)) (Database Name) :=
  importResult db name
    (Manifest.RenderedPositional.scan admission maxDirectoryBytes keys encoding options convert listing
      limits lookup projection keep budget)

end Silmaril.Formats.Relational.NamedTable.FromRenderedPositional
