module

meta import Silmaril.Formats.Relational.NamedTable.Date32.Export.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable.Date32
open Silmaril.Formats.Relational.NamedTable.Date32.Export

private meta def bounds : Limits :=
  ⟨16, ⟨1, 4096, {}, ⟨{}, 64, ⟨64, 256, ⟨16, 64⟩, 0⟩⟩⟩, {}⟩

private meta def tableName : String := "dates"

private meta def fromSlots (field : String) (nullable : Bool) (slots : List Slot) :
    Database String :=
  Function.update (fun _ => none) tableName (some ⟨schema field nullable, rows field nullable slots⟩)

/-- Both columns deliberately share the same descriptor. The ordinal selects the data. -/
private meta def pairSchema : Scan.Schema String Date.Events.Kind :=
  ⟨2, fun _ => ("日付", .date32 true)⟩

private meta def fromPairs (pairs : List (Slot × Slot)) : Database String :=
  Function.update (fun _ => none) tableName
    (some ⟨pairSchema, pairs.map fun pair index => if index.val = 0 then pair.1 else pair.2⟩)

private meta def rejects (db : Database String) (column : Column) (cause : Error)
    (limits : Limits := bounds) (name : String := tableName) : Bool :=
  match convert db name column limits with
  | .error actual => actual == cause
  | .ok _ => false

private meta def emit (path : System.FilePath) (db : Database String) (column : Column) : IO Unit := do
  match convert db tableName column bounds with
  | .ok wire => IO.FS.writeBinFile path wire.data
  | .error cause => throw (IO.userError (reprStr cause))

private meta def importAndEmit (path : System.FilePath) (field : String) (nullable : Bool)
    (input : Bytes) : IO Unit := do
  let .ok db := importParquet (fun _ => none) tableName field nullable {} input
    | throw (IO.userError "Named DATE import failed")
  emit path db ⟨0, field, nullable⟩

private meta def one : Database String := fromSlots "日付" true [some (-1)]

#guard rejects one ⟨0, "日付", true⟩ .missingName { bounds with maxRows := 0 } "missing"
#guard rejects one ⟨1, "日付", true⟩ (.columnIndex 1 1)
#guard rejects one ⟨0, "other", false⟩ (.fieldMismatch "日付") { bounds with maxRows := 0 }
#guard rejects one ⟨0, "日付", false⟩ (.kindMismatch (.date32 true)) { bounds with maxRows := 0 }
#guard rejects one ⟨0, "日付", true⟩ (.rowLimit 1 0)
  { bounds with maxRows := 0, writer.maxFileBytes := 0 }
#guard rejects (fromSlots "日付" false [none]) ⟨0, "日付", false⟩ (.write .requiredNull)
#guard rejects one ⟨0, "日付", true⟩ (.write (.writer .fileLimit))
  { bounds with writer.maxFileBytes := 0 }
#guard rejects one ⟨0, "日付", true⟩ (.write (.readback (.scan .rowLimit)))
  { bounds with readback.scan.maxRows := 0 }
#guard select (fromPairs [(some (-1), none), (none, some 2), (some 3, none)])
  tableName ⟨1, "日付", true⟩ 3 == .ok [none, some 2, none]
