module

public import Silmaril.Formats.Parquet.FlatColumn.Defs
public import Silmaril.Formats.Parquet.Int96.Page.Defs

/-! Read one selected INT96 leaf from a bounded immutable Parquet snapshot. -/

public section

namespace Silmaril.Formats.Parquet.Int96.File

structure Limits where
  snapshot : Snapshot.Limits := {}
  column : FlatColumn.Limits := {}
  maxFileBytes : Nat := 256 * 1024 * 1024
  maxTotalRows : Nat := 1024 * 1024

inductive OpenError where
  | fileByteLimit (maximum actual : Nat)
  | snapshot (cause : Snapshot.Error Unit)
  | rowLimit (maximum actual : Nat)
  | binding (cause : FlatColumn.BindError)
  deriving DecidableEq, Repr

abbrev ReadError := FlatColumn.Error Page.Error
abbrev Slots (interpretation : Policy) := List (Option (Page.Value interpretation))

/-- The binding uses the exact checked snapshot, column name and flat layout.
The interpretation supplied at open fixes the type of subsequent reads. -/
structure Checked (name : String) (layout : FlatColumn.Layout) (interpretation : Policy) where
  private mk ::
  snapshot : Snapshot.Checked
  binding : FlatColumn.Binding snapshot ⟨name, .int96, layout⟩
  columnLimits : FlatColumn.Limits

/-- Check the file and the declared total row budget before admitting the
selected physical leaf. The footer never chooses the interpretation. -/
def openFile (limits : Limits) (source : Bytes) (name : String)
    (layout : FlatColumn.Layout) (interpretation : Policy) :
    Except OpenError (Checked name layout interpretation) := do
  if limits.maxFileBytes < source.length then
    Except.error (.fileByteLimit limits.maxFileBytes source.length)
  let snapshot ← (Snapshot.check (Failure := Unit) limits.snapshot source).mapError .snapshot
  if limits.maxTotalRows < snapshot.metadata.numRows.toNat then
    Except.error (.rowLimit limits.maxTotalRows snapshot.metadata.numRows.toNat)
  let binding ← (FlatColumn.bindColumn snapshot ⟨name, .int96, layout⟩).mapError .binding
  return ⟨snapshot, binding, limits.column⟩

def plain : FlatColumn.Policy := ⟨0, .v1AndV2⟩

/-- The callback keeps the original codec, header and body, together with
the exact slot error from the INT96 page decoder. -/
def decodePage (interpretation : Policy) (limits : FlatColumn.Limits) :
    FlatColumn.DecodePage (Page.Value interpretation) Page.Error :=
  fun leaf metadata header body =>
    Page.decode interpretation leaf metadata.codec header
      ⟨limits.maxPageBytes, limits.maxPageBytes, ⟨limits.maxRows, limits.maxPageBytes⟩, 0⟩ body

variable {name : String} {layout : FlatColumn.Layout} {interpretation : Policy}

/-- Read one selected group, retaining the full physical reader error. -/
@[expose] def Checked.readGroup (checked : Checked name layout interpretation) (index : Nat) :
    Except ReadError (Slots interpretation) :=
  FlatColumn.readColumn checked.binding checked.columnLimits plain
    (decodePage interpretation checked.columnLimits) index

/-- A whole-file outcome keeps each complete group and the unchanged first
read error, if any. Open errors are returned separately. -/
structure Trace (interpretation : Policy) where
  groups : List (Slots interpretation)
  failure : Option ReadError

/-- Read in footer order, publishing a group only after every page succeeds. -/
def Checked.readAll (checked : Checked name layout interpretation) : Trace interpretation :=
  loop checked (List.range checked.snapshot.groupCount) []
where
  loop (checked : Checked name layout interpretation) :
      List Nat → List (Slots interpretation) → Trace interpretation
    | [], reversed => ⟨reversed.reverse, none⟩
    | index :: rest, reversed =>
      match checked.readGroup index with
      | .error cause => ⟨reversed.reverse, some cause⟩
      | .ok slots => loop checked rest (slots :: reversed)

def readFile (limits : Limits) (source : Bytes) (name : String)
    (layout : FlatColumn.Layout) (interpretation : Policy) :
    Except OpenError (Trace interpretation) :=
  (openFile limits source name layout interpretation).map Checked.readAll

end Silmaril.Formats.Parquet.Int96.File
