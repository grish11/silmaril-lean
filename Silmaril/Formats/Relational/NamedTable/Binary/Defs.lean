module

public import Silmaril.Formats.Relational.NamedTable.Defs
public import Silmaril.Formats.Relational.BinaryObservation.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.File.Defs

/-! Atomic named imports of one selected raw Parquet BYTE_ARRAY leaf or
one checked Arrow BinaryView IPC field. -/

@[expose] public section

namespace Silmaril.Formats.Relational.NamedTable.Binary

open Arrow.BinaryView
open Silmaril.Formats.Parquet
open Parquet.Plain.ByteArray
open Relational.BinaryObservation

abbrev Database (Name : Type*) := NamedTable.Packed Name String Cell

def layoutOf (field : Field) : FlatColumn.Layout :=
  if field.nullable then .optional else .required

/-- Retain table width, exact labels, and nullable slots while normalizing
the Parquet byte-carrier and field kind. -/
def parquetObservation (source : Silmaril.Relational.Scan.Observation String File.Value) : Observation :=
  let schema : Silmaril.Relational.Scan.Schema String Bool :=
    ⟨source.schema.width, fun index =>
      let (name, layout) := source.schema.kind index
      (name, decide (layout = .optional))⟩
  ⟨schema, source.rows.map fun row index => (row index).map Bytes.toList⟩

/-- The original termination and any completed prefix stay with a collected
Parquet observation. The named gate decides whether it may be inserted. -/
def collectParquet (limits : File.Limits) (input : Bytes) (selected : Field) :
    Except File.Error (Arrow.Events.Observation String Cell File.Error) :=
  (File.readAll limits input selected.name (layoutOf selected)).collect.map fun observed =>
    ⟨parquetObservation observed.table, observed.termination⟩

/-- The checked IPC reader supplies an observation only through exact EOS.
The actual field goes to the named gate for its descriptor check. -/
def collectIpc (ipc : Arrow.Limits) (limits : Column.Limits) (input : KBytes) :
    Except IpcError (Arrow.Events.Observation String Cell IpcError) :=
  match Stream.read ipc limits input with
  | .error cause => .error (.reader cause)
  | .ok ⟨⟨name, nullable, .binary⟩, batches⟩ =>
    .ok ⟨observation ⟨name, nullable⟩ (ipcSlots batches), .eos⟩
  | .ok ⟨⟨_, _, .utf8⟩, _⟩ => .error .utf8View

def importParquet {Name : Type*} [DecidableEq Name]
    (db : Database Name) (name : Name) (expected selected : Field) (limits : File.Limits) (input : Bytes) :
    Except (ImportError File.Error) (Database Name) :=
  NamedTable.importCollected db name expected.schema (collectParquet limits input selected)

/-- The atomic IPC reader returns its failures without a table. Preserve the
indexed batch cause and classify it as a read error after the named gate. -/
def importIpc {Name : Type*} [DecidableEq Name]
    (db : Database Name) (name : Name) (expected : Field) (ipc : Arrow.Limits) (limits : Column.Limits)
    (input : KBytes) : Except (ImportError IpcError) (Database Name) :=
  (NamedTable.importCollected db name expected.schema (collectIpc ipc limits input)).mapError fun
    | .openError (.reader (.batch index cause)) => .readError (.reader (.batch index cause))
    | cause => cause

end Silmaril.Formats.Relational.NamedTable.Binary
