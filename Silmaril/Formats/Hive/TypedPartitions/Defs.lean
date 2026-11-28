module

public import Silmaril.Formats.Hive.PartitionPath.Defs
public import Silmaril.Semantics.Relational.Scan.Defs

/-!
# Typed Hive partition columns

The input is an ordered manifest of already available physical rows and decoded
partition entries. Each manifest entry supplies one typed, nullable tuple of
virtual values for all its rows. The augmented schema places physical columns
first and virtual columns in declared order. This layer has no file operations.
-/

@[expose] public section

namespace Silmaril.Formats.Hive.TypedPartitions

open Silmaril.Relational

inductive Missing where
  | reject
  | asNull
  deriving Repr

structure Field (Kind : Type*) where
  name : String
  kind : Kind
  missing : Missing := .reject

/-- The array determines the order of the virtual columns. -/
structure PartitionSchema (Kind : Type*) where
  fields : Array (Field Kind)

universe u v

variable {Kind : Type u} {Value : Kind → Type v}

namespace PartitionSchema

def toScan (schema : PartitionSchema Kind) : Scan.Schema String Kind :=
  ⟨schema.fields.size, fun i => (schema.fields[i].name, schema.fields[i].kind)⟩

def keys (schema : PartitionSchema Kind) : List String :=
  schema.fields.toList.map (·.name)

def extend (schema : PartitionSchema Kind) (physical : Scan.Schema String Kind) :
    Scan.Schema String Kind :=
  ⟨physical.width + schema.toScan.width, Fin.addCases physical.kind schema.toScan.kind⟩

end PartitionSchema

/-- A caller checks present text at the field's declared type. Explicit null
and synthesized null never call the converter. -/
abbrev Convert (Value : Kind → Type*) (Failure : Type*) :=
  (field : Field Kind) → String → Except Failure (Value field.kind)

inductive Error (Failure : Type*) where
  | schemaKeys (reason : PartitionPath.Error)
  | physicalCollision (key : String)
  | partitionKeys (reason : PartitionPath.Error)
  | unknownKey (key : String)
  | missingKey (key : String)
  | conversion (key : String) (reason : Failure)
  deriving BEq, Repr

/-- Check virtual names, then reject any virtual name used by a physical column.
Physical columns keep their original positions and identities. -/
def checkSchema {Failure : Type*} (physical : Scan.Schema String Kind)
    (schema : PartitionSchema Kind) : Except (Error Failure) Unit := do
  (PartitionPath.validateKeys schema.keys).mapError Error.schemaKeys
  let physicalNames := List.ofFn fun i => (physical.kind i).1
  match schema.keys.find? physicalNames.contains with
  | some key => .error (.physicalCollision key)
  | none => .ok ()

def decodeField {Failure : Type*} (convert : Convert Value Failure)
    (entries : PartitionPath.Partition) (field : Field Kind) :
    Except (Error Failure) (Option (Value field.kind)) :=
  match PartitionPath.lookup field.name entries with
  | none =>
    match field.missing with
    | .reject => .error (.missingKey field.name)
    | .asNull => .ok none
  | some none => .ok none
  | some (some text) => ((convert field text).map some).mapError (Error.conversion field.name)

/-- Check raw keys even when they came from a caller other than the path parser.
Errors are reported before any field conversion, which then runs in schema order. -/
def decode {Failure : Type*} (schema : PartitionSchema Kind) (convert : Convert Value Failure)
    (entries : PartitionPath.Partition) : Except (Error Failure) (Scan.Row schema.toScan Value) :=
  match PartitionPath.validateKeys (entries.map Prod.fst) with
  | .error reason => .error (.partitionKeys reason)
  | .ok () =>
    match entries.find? (fun entry => !schema.keys.contains entry.1) with
    | some entry => .error (.unknownKey entry.1)
    | none => sequenceFin schema.fields.size (fun i => decodeField convert entries schema.fields[i])
where
  sequenceFin : (n : Nat) → {Result : Fin n → Type v} →
      ((i : Fin n) → Except (Error Failure) (Result i)) →
      Except (Error Failure) ((i : Fin n) → Result i)
    | 0, _, _ => .ok (fun i => nomatch i)
    | n + 1, _, check => do
      let first ← check 0
      let rest ← sequenceFin n (fun i => check i.succ)
      pure (Fin.cases first rest)

structure InputPartition (physical : Scan.Schema String Kind) (Value : Kind → Type*) where
  entries : PartitionPath.Partition
  rows : Scan.Table physical Value

structure TypedPartition (physical : Scan.Schema String Kind)
    (schema : PartitionSchema Kind) (Value : Kind → Type*) where
  cells : Scan.Row schema.toScan Value
  rows : Scan.Table physical Value

/-- Validate the schema even for an empty manifest. Validate each binding even
for a partition with zero physical rows. The result carries cells in schema order. -/
def prepare {Failure : Type*} {physical : Scan.Schema String Kind}
    (schema : PartitionSchema Kind) (convert : Convert Value Failure)
    (manifest : List (InputPartition physical Value)) :
    Except (Error Failure) (List (TypedPartition physical schema Value)) :=
  match checkSchema physical schema with
  | .error reason => .error reason
  | .ok () =>
    manifest.mapM fun partition => do
      let cells ← decode schema convert partition.entries
      pure ⟨cells, partition.rows⟩

variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

def extendRow (row : Scan.Row physical Value) (cells : Scan.Row schema.toScan Value) :
    Scan.Row (schema.extend physical) Value :=
  Fin.addCases (motive := fun i => Option (Value ((schema.extend physical).kind i).2))
    (fun i => cast (by simp [PartitionSchema.extend]) (row i))
    (fun i => cast (by simp [PartitionSchema.extend]) (cells i))

def physicalCells (row : Scan.Row (schema.extend physical) Value) : Scan.Row physical Value :=
  fun i => cast (by simp [PartitionSchema.extend]) (row (i.castAdd schema.toScan.width))

def partitionCells (row : Scan.Row (schema.extend physical) Value) :
    Scan.Row schema.toScan Value :=
  fun i => cast (by simp [PartitionSchema.extend]) (row (i.natAdd physical.width))

def TypedPartition.materialize (partition : TypedPartition physical schema Value) :
    Scan.Table (schema.extend physical) Value :=
  partition.rows.map (fun row => extendRow row partition.cells)

def materialize (manifest : List (TypedPartition physical schema Value)) :
    Scan.Table (schema.extend physical) Value :=
  manifest.flatMap TypedPartition.materialize

/-- Evaluate a partition-only predicate once per manifest entry on already
available rows. False and unknown both discard that partition's rows. -/
def scanPartitions (projection : Scan.Projection (schema.extend physical))
    (predicate : Scan.Predicate schema.toScan Value)
    (manifest : List (TypedPartition physical schema Value)) : Scan.Table projection.schema Value :=
  manifest.flatMap fun partition =>
    if (predicate partition.cells).getD false then projection.project partition.materialize else []

end Silmaril.Formats.Hive.TypedPartitions
