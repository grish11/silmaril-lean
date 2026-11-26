module

public import Silmaril.Formats.Relational.NamedTable.MixedIpc.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs

/-! Compose checked selected Parquet groups, mixed IPC emission, and an
atomic named-table insertion. -/

@[expose] public section

namespace Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int32ByteArrayGroup

def descriptor (int32 byteArray : Field) : Descriptor :=
  let schema := Prepare.Schema.ofSelection int32 byteArray
  ⟨false, (schema.intName, schema.intNullable), (schema.viewName, schema.viewNullable)⟩

def groupPairs (rows : List Row) : List Pair :=
  rows.map fun row => (row.1, row.2.map Bytes.toList)

/-- IPC retains a batch for each group. `Prepared.table` flattens those batches
in order, keeping the two values of each row together. -/
def observation (int32 byteArray : Field) (groups : List (List Row)) : Prepared :=
  ⟨descriptor int32 byteArray, groups.map groupPairs⟩

inductive Error where
  | conversion (cause : ToIpc.Error)
  | ipcImport (cause : NamedTable.ImportError MixedIpc.Error)
  deriving DecidableEq

/-- The existing converter exhausts the checked source before emission.
The existing IPC import requires exact EOS and a vacant destination. -/
def importNamed {Name : Type*} [DecidableEq Name]
    (db : Database Name) (name : Name) (parquet : File.Limits) (ipc : Limits)
    (input : Bytes) (int32 byteArray : Field) : Except Error (Database Name) :=
  match ToIpc.convert parquet ipc.mixed input int32 byteArray with
  | .error cause => .error (.conversion cause)
  | .ok wire => (importIpc db name (descriptor int32 byteArray) ipc wire).mapError .ipcImport

end Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet
