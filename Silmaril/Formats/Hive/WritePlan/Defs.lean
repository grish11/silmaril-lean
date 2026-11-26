module

public import Silmaril.Formats.Hive.TypedPartitions.Defs

/-!
# Pure Hive write-side routing

Encode the virtual cells of each row as a checked relative Hive directory.
Group physical payloads by directory in first-occurrence order, preserving
every row in each group. No filenames or file contents are allocated.
-/

@[expose] public section

namespace Silmaril.Formats.Hive.WritePlan

open Silmaril.Relational
open Silmaril.Formats.Hive.TypedPartitions (Field PartitionSchema partitionCells physicalCells)

variable {Kind : Type*} {Value : Kind → Type*} {Failure : Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

/-- A checked encoder for present cells. Nulls bypass the encoder. -/
abbrev Encode (Value : Kind → Type*) (Failure : Type*) :=
  (field : Field Kind) → Value field.kind → Except Failure String

inductive RowError (Failure : Type*) where
  | encode (key : String) (reason : Failure)
  | render (reason : PartitionPath.Error)
  | parse (reason : PartitionPath.Error)
  deriving BEq, Repr

inductive Error (Failure : Type*) where
  | schema (reason : TypedPartitions.Error Failure)
  | row (index : Nat) (reason : RowError Failure)
  deriving BEq, Repr

/-- Empty directory denotes the dataset root. Even at width zero, each
position in the physical row list contributes one row to the payload. -/
structure Bucket (physical : Scan.Schema String Kind) (Value : Kind → Type*) where
  directory : String
  rows : Scan.Table physical Value

def encodeEntries (encode : Encode Value Failure) (cells : Scan.Row schema.toScan Value) :
    Except (RowError Failure) PartitionPath.Partition :=
  (List.finRange schema.fields.size).mapM fun i =>
    let field := schema.fields[i]
    match cells i with
    | none => .ok (field.name, none)
    | some value => ((encode field value).mapError (RowError.encode field.name)).map
        (fun text => (field.name, some text))

/-- Use the existing render and parse policies for a directory, after
encoding all present virtual cells in declared field order. -/
def classifyRow (options : PartitionPath.Options) (encode : Encode Value Failure)
    (row : Scan.Row (schema.extend physical) Value) :
    Except (RowError Failure) (String × Scan.Row physical Value) :=
  match encodeEntries encode (partitionCells row) with
  | .error reason => .error reason
  | .ok entries =>
    match PartitionPath.render options entries with
    | .error reason => .error (.render reason)
    | .ok directory =>
      match PartitionPath.parse options directory with
      | .error reason => .error (.parse reason)
      | .ok _ => .ok (directory, physicalCells row)

def classify (options : PartitionPath.Options) (encode : Encode Value Failure)
    (rows : Scan.Table (schema.extend physical) Value) (offset : Nat := 0) :
    Except (Error Failure) (List (String × Scan.Row physical Value)) :=
  (rows.zipIdx offset).mapM fun entry => (classifyRow options encode entry.1).mapError (Error.row entry.2)

/-- Remove the current directory's rows in one stable partition and continue
on the remaining occurrences. -/
def groupRows : List (String × Scan.Row physical Value) → List (Bucket physical Value)
  | [] => []
  | (directory, row) :: rest =>
    let groups := rest.partition (fun entry => entry.1 == directory)
    ⟨directory, row :: groups.1.map Prod.snd⟩ :: groupRows groups.2
termination_by rows => rows.length
decreasing_by
  simp only [List.partition_eq_filter_filter]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Choose directory order separately, then select the payload for each
directory by filtering the full classified input. -/
def referenceGroups (classified : List (String × Scan.Row physical Value)) :
    List (Bucket physical Value) :=
  (classified.map Prod.fst).eraseDups.map fun directory =>
    ⟨directory, (classified.filter (fun entry => entry.1 == directory)).map Prod.snd⟩

/-- Validate the schema first, then route the rows or return the first
indexed failure. The partition names, options and checked encoder determine
the directory, and all remaining cells stay at their original physical schema. -/
def plan (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (options : PartitionPath.Options) (encode : Encode Value Failure)
    (rows : Scan.Table (schema.extend physical) Value) : Except (Error Failure) (List (Bucket physical Value)) :=
  match TypedPartitions.checkSchema physical schema with
  | .error reason => .error (.schema reason)
  | .ok () => (classify options encode rows).map groupRows

def reference (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (options : PartitionPath.Options) (encode : Encode Value Failure)
    (rows : Scan.Table (schema.extend physical) Value) : Except (Error Failure) (List (Bucket physical Value)) :=
  match TypedPartitions.checkSchema physical schema with
  | .error reason => .error (.schema reason)
  | .ok () => (classify options encode rows).map referenceGroups

end Silmaril.Formats.Hive.WritePlan
