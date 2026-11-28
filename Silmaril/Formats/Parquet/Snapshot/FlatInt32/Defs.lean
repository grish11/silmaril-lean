module

public import Silmaril.Formats.Parquet.Snapshot.Defs
public import Silmaril.Formats.Parquet.FlatScan.Scalar.Defs

/-! Open checked flat, uncompressed PLAIN INT32 Parquet bytes as Arrow events. -/

public section

namespace Silmaril.Formats.Parquet.Snapshot.FlatInt32

open Silmaril.Relational Silmaril.Formats.Arrow

abbrev Cell (_ : Unit) := Int32

structure Limits where
  snapshot : Snapshot.Limits := {}
  groups : FlatScan.Limits := {}
  pages : ScalarPage.Limits := ⟨16 * 1024 * 1024, 16 * 1024 * 1024, ⟨1024 * 1024, 16 * 1024 * 1024⟩, 0⟩

inductive Error (InputFailure : Type) where
  | lookup (reason : InputFailure)
  | profile (reason : FlatScan.Error FlatScan.AdapterError)
  | schemaNames (expected actual : List String)
  | rowWidth (expected actual : Nat)
  deriving DecidableEq, Repr

private def typedRow {InputFailure : Type} (schema : Scan.Schema String Unit) (row : List (Option Int32)) :
    Except (Error InputFailure) (Scan.Row schema Cell) :=
  if width : row.length = schema.width then
    .ok (fun index => row[index.val]'(width.symm ▸ index.isLt))
  else
    .error (.rowWidth schema.width row.length)

/-- Validate the supported flat schema and check its labels in the caller's
order at open. Decode only the group supplied by the snapshot cursor. -/
def bind {InputFailure : Type} (limits : Limits) (schema : Scan.Schema String Unit) :
    Snapshot.Bind schema Cell (Error InputFailure) := fun metadata => do
  let fields ← (FlatScan.flatSchema limits.groups metadata.schema).mapError .profile
  let expected := List.ofFn (fun index => (schema.kind index).1)
  let actual := fields.map (·.name)
  if expected ≠ actual then throw (.schemaNames expected actual)
  pure fun snapshot _ group => do
    let page := FlatScan.decodeInt32Page limits.pages
    let batch ← (FlatScan.scanRowGroup limits.groups page snapshot.bytes snapshot.footer.start
      metadata.schema group).mapError .profile
    batch.rows.mapM (typedRow schema)

/-- Read a finite byte snapshot through EOF or the first indexed error. -/
def readAll (limits : Limits) (schema : Scan.Schema String Unit) (bytes : Bytes) :
    Events.EventStream String Cell (Snapshot.Error (Error Unit)) :=
  Snapshot.readAll limits.snapshot (bind limits schema) bytes

end Silmaril.Formats.Parquet.Snapshot.FlatInt32
