module

public import Silmaril.Formats.Parquet.Int96.Dictionary.Defs
public import Silmaril.Formats.Parquet.Int96.File.Defs

/-! One dictionary-encoded INT96 leaf in a bounded immutable Parquet file. -/

public section

namespace Silmaril.Formats.Parquet.Int96.Dictionary.File

structure Limits where
  snapshot : Snapshot.Limits := {}
  chunk : Dictionary.Limits := {}
  maxFileBytes : Nat := 256 * 1024 * 1024
  maxTotalRows : Nat := 1024 * 1024

def Limits.bindingLimits (limits : Limits) : Int96.File.Limits :=
  { snapshot := limits.snapshot, maxFileBytes := limits.maxFileBytes, maxTotalRows := limits.maxTotalRows }

inductive SelectionError where
  | groupIndex (index : Nat)
  | columnIndex (group column : Nat)
  | association (group column : Nat)
  | bounds (group column : Nat)
  deriving DecidableEq, Repr

inductive PreflightError where
  | selection (cause : SelectionError)
  | overlap (firstGroup secondGroup : Nat)
  deriving DecidableEq, Repr

inductive OpenError where
  | binding (cause : Int96.File.OpenError)
  | preflight (cause : PreflightError)
  deriving DecidableEq, Repr

inductive ReadError where
  | selection (cause : SelectionError)
  | chunk (group column : Nat) (name : String) (cause : Dictionary.Error)
  deriving DecidableEq, Repr

structure Selected where
  group : Footer.RowGroup
  column : Footer.ColumnChunk
  span : Footer.Span

variable {name : String} {layout : FlatColumn.Layout} {interpretation : Policy}

/-- Select the original group and column by ordinal. Page encoding admission
is left to the per-group dictionary decoder. -/
@[expose] def select (bound : Int96.File.Checked name layout interpretation) (index : Nat) :
    Except SelectionError Selected := do
  let ordinal := bound.binding.columnOrdinal
  let some group := bound.snapshot.groupAt index | Except.error (.groupIndex index)
  let some column := group.columns[ordinal]? | Except.error (.columnIndex index ordinal)
  let metadata := column.metadata
  if metadata.pathInSchema ≠ [bound.binding.leaf.name] ∨ metadata.physicalType ≠ .int96 ∨
      metadata.numValues ≠ group.numRows then Except.error (.association index ordinal)
  let some span := Parquet.Page.columnSpan bound.snapshot.footer.start metadata |
    Except.error (.bounds index ordinal)
  return ⟨group, column, span⟩

def spans (bound : Int96.File.Checked name layout interpretation) :
    Except PreflightError (List (Nat × Footer.Span)) :=
  (List.range bound.snapshot.groupCount).mapM fun index =>
    ((select bound index).map fun selected => (index, selected.span)).mapError .selection

/-- The sort is used for checking intervals. Read order remains footer order. -/
def byStart (left right : Nat × Footer.Span) : Bool :=
  left.2.start ≤ right.2.start

def checkNeighbors : List (Nat × Footer.Span) → Except PreflightError Unit
  | left :: right :: tail =>
    if left.2.stop ≤ right.2.start then checkNeighbors (right :: tail)
    else .error (.overlap left.1 right.1)
  | _ => .ok ()

def preflight (bound : Int96.File.Checked name layout interpretation) : Except PreflightError Unit := do
  let ranges ← spans bound
  checkNeighbors (ranges.mergeSort byStart)

structure Checked (name : String) (layout : FlatColumn.Layout) (interpretation : Policy) where
  private mk ::
  bound : Int96.File.Checked name layout interpretation
  chunkLimits : Dictionary.Limits

def openFile (limits : Limits) (source : Bytes) (name : String)
    (layout : FlatColumn.Layout) (interpretation : Policy) :
    Except OpenError (Checked name layout interpretation) := do
  let bound ← (Int96.File.openFile limits.bindingLimits source name layout interpretation).mapError .binding
  (preflight bound).mapError .preflight
  return ⟨bound, limits.chunk⟩

/-- Read the selected chunk from the retained source. The chunk reader's
absolute offsets, dictionary entry and logical slot errors pass through. -/
@[expose] def Checked.readGroup (checked : Checked name layout interpretation) (index : Nat) :
    Except ReadError (Slots interpretation) := do
  let bound := checked.bound
  let selected ← (select bound index).mapError .selection
  (Dictionary.read checked.chunkLimits interpretation bound.snapshot.bytes bound.snapshot.footer.start
    selected.group.numRows.toNat bound.binding.leaf selected.column.metadata).mapError
      (.chunk index bound.binding.columnOrdinal name)

structure Trace (interpretation : Policy) where
  groups : List (Slots interpretation)
  failure : Option ReadError

/-- Publish only complete groups, stopping at the first original read error. -/
def Checked.readAll (checked : Checked name layout interpretation) : Trace interpretation :=
  loop checked (List.range checked.bound.snapshot.groupCount) []
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

end Silmaril.Formats.Parquet.Int96.Dictionary.File
