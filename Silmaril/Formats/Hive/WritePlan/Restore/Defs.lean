module

public import Silmaril.Formats.Hive.WritePlan.Defs

/-!
# Reconstruct typed rows from a Hive write plan

Read each directory using the Hive partition profile and put the typed
virtual cells back onto the bucket's physical rows. Reconstruction
materializes in bucket order and in physical row order inside a bucket.
-/

@[expose] public section

namespace Silmaril.Formats.Hive.WritePlan

open Silmaril.Relational
open Silmaril.Formats.Hive.TypedPartitions (Convert PartitionSchema)

variable {Kind : Type*} {Value : Kind → Type*} {Failure : Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

inductive RestoreError (Failure : Type*) where
  | schema (reason : TypedPartitions.Error Failure)
  | path (directory : String) (reason : PartitionPath.Error)
  | binding (directory : String) (reason : TypedPartitions.Error Failure)
  deriving BEq, Repr

/-- A left inverse on successful encodings of present cells. Nulls bypass
both callbacks. This law permits either callback to reject other inputs. -/
def CellLeftInverse {EncodeFailure DecodeFailure : Type*} (schema : PartitionSchema Kind)
    (encode : Encode Value EncodeFailure) (decode : Convert Value DecodeFailure) : Prop :=
  ∀ (i : Fin schema.fields.size) (value : Value (schema.fields[i]).kind) (text : String),
    encode schema.fields[i] value = .ok text → decode schema.fields[i] text = .ok value

def decodeDirectory (schema : PartitionSchema Kind) (options : PartitionPath.Options)
    (decode : Convert Value Failure) (directory : String) :
    Except (RestoreError Failure) (Scan.Row schema.toScan Value) :=
  match PartitionPath.parse options directory with
  | .error reason => .error (.path directory reason)
  | .ok entries =>
    (TypedPartitions.decode schema decode entries).mapError (RestoreError.binding directory)

/-- Check the schema, then bind each supplied directory in order. The first
path or binding failure aborts the reconstruction. -/
def restore (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (options : PartitionPath.Options) (decode : Convert Value Failure)
    (buckets : List (Bucket physical Value)) :
    Except (RestoreError Failure) (Scan.Table (schema.extend physical) Value) :=
  match TypedPartitions.checkSchema physical schema with
  | .error reason => .error (.schema reason)
  | .ok () =>
    let bound := buckets.mapM fun bucket =>
      (decodeDirectory schema options decode bucket.directory).map fun cells =>
        ({ cells, rows := bucket.rows } : TypedPartitions.TypedPartition physical schema Value)
    bound.map TypedPartitions.materialize

def taggedRows (options : PartitionPath.Options) (encode : Encode Value Failure)
    (rows : Scan.Table (schema.extend physical) Value) :
    List (String × Scan.Row (schema.extend physical) Value) :=
  rows.filterMap fun row =>
    (classifyRow options encode row).toOption.map fun admitted => (admitted.1, row)

/-- Reference over the full original rows. Successful planning ensures that
every row contributes a tag. The first-seen directory list gives group
order, and filtering the original list gives stable order within a group. -/
def groupOriginalRows (options : PartitionPath.Options) (encode : Encode Value Failure)
    (rows : Scan.Table (schema.extend physical) Value) : Scan.Table (schema.extend physical) Value :=
  let tagged := taggedRows options encode rows
  (tagged.map Prod.fst).eraseDups.flatMap fun directory =>
    (tagged.filter (fun entry => entry.1 == directory)).map Prod.snd

end Silmaril.Formats.Hive.WritePlan
