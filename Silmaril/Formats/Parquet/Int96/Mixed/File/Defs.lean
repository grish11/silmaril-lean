module

public import Silmaril.Formats.Parquet.Int96.Dictionary.File.Defs
public import Silmaril.Formats.Parquet.Int96.Mixed.Defs

/-! Opt-in mixed-encoding reads of one INT96 leaf in a checked Parquet file. -/

public section

namespace Silmaril.Formats.Parquet.Int96.Mixed.File

abbrev Limits := Dictionary.File.Limits
abbrev OpenError := Dictionary.File.OpenError

inductive ReadError where
  | selection (cause : Dictionary.File.SelectionError)
  | chunk (group column : Nat) (name : String) (cause : Mixed.Error)
  deriving DecidableEq, Repr

/-- The retained capability checks footer association and disjoint chunk
intervals. The mixed profile is chosen explicitly at this entry point. -/
structure Checked (name : String) (layout : FlatColumn.Layout) (interpretation : Policy) where
  private mk ::
  selection : Dictionary.File.Checked name layout interpretation

def openFile (limits : Limits) (source : Bytes) (name : String)
    (layout : FlatColumn.Layout) (interpretation : Policy) :
    Except OpenError (Checked name layout interpretation) :=
  (Dictionary.File.openFile limits source name layout interpretation).map Checked.mk

variable {name : String} {layout : FlatColumn.Layout} {interpretation : Policy}

/-- Resolve the original group and column, then use the mixed chunk decoder
on that snapshot. Its chunk, frame and slot errors pass through intact. -/
def Checked.readGroup (checked : Checked name layout interpretation) (index : Nat) :
    Except ReadError (Dictionary.Slots interpretation) := do
  let bound := checked.selection.bound
  let selected ← (Dictionary.File.select bound index).mapError .selection
  (Mixed.read checked.selection.chunkLimits interpretation bound.snapshot.bytes bound.snapshot.footer.start
    selected.group.numRows.toNat bound.binding.leaf selected.column.metadata).mapError
      (.chunk index bound.binding.columnOrdinal name)

structure Trace (interpretation : Policy) where
  groups : List (Dictionary.Slots interpretation)
  failure : Option ReadError

private def step (checked : Checked name layout interpretation)
    (reversed : List (Dictionary.Slots interpretation)) (index : Nat) :
    Except (Trace interpretation) (List (Dictionary.Slots interpretation)) :=
  match checked.readGroup index with
  | .ok slots => .ok (slots :: reversed)
  | .error cause => .error ⟨reversed.reverse, some cause⟩

private def collect (checked : Checked name layout interpretation) (indices : List Nat)
    (reversed : List (Dictionary.Slots interpretation)) : Trace interpretation :=
  match indices.foldlM (step checked) reversed with
  | .ok groups => ⟨groups.reverse, none⟩
  | .error trace => trace

/-- Retain each complete group in footer order, stopping at the first
failing group. -/
def Checked.readAll (checked : Checked name layout interpretation) : Trace interpretation :=
  collect checked (List.range checked.selection.bound.snapshot.groupCount) []

def readFile (limits : Limits) (source : Bytes) (name : String)
    (layout : FlatColumn.Layout) (interpretation : Policy) :
    Except OpenError (Trace interpretation) :=
  (openFile limits source name layout interpretation).map Checked.readAll

end Silmaril.Formats.Parquet.Int96.Mixed.File
