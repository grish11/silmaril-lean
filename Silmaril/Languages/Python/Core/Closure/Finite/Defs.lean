module

public import Silmaril.Languages.Python.Core.Closure.Defs
public import Silmaril.Semantics.Operational.Environment.Finite.Defs
public import Silmaril.Semantics.Operational.Projection.Defs

/-! # Finite presentations for the Python closure store interface -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Closure.Finite

open Semantics.Operational
open Environment.Finite (view)

abbrev Rows := AList (fun _ : Nat => Value)

/-- Allocation is represented by the frontier. Rows only store bound
values, and their addresses are allocated. -/
structure HeapTable where
  next : Nat
  rows : Rows
  bounded : ∀ address value, view rows address = some value → address < next

namespace HeapTable

def empty : HeapTable :=
  ⟨0, ∅, fun _ _ found => by cases found⟩

def project (table : HeapTable) : Heap :=
  ⟨table.next, view table.rows⟩

def reserve (table : HeapTable) (count : Nat) : HeapTable :=
  ⟨table.next + count, table.rows,
    fun address value found => Nat.lt_of_lt_of_le (table.bounded address value found) (Nat.le_add_right ..)⟩

def bind (table : HeapTable) (identity : CellId) (value : Value)
    (allocated : identity.address < table.next) : HeapTable :=
  ⟨table.next, table.rows.insert identity.address value, by
    intro address stored found
    by_cases same : address = identity.address
    · exact same ▸ allocated
    · apply table.bounded address stored
      simpa [view, AList.lookup_insert_ne same] using found⟩

def write (table : HeapTable) (identity : CellId) (value : Value) : Option HeapTable :=
  if allocated : identity.address < table.next then some (table.bind identity value allocated) else none

end HeapTable

variable {layout : Layout}

/-- Frame maps already have finite slot domains. Retain their values and
cell identities verbatim, including aliasing between captured slots. -/
structure Snapshot (layout : Layout) where
  heap : HeapTable
  frame : Frame layout

def Snapshot.project (source : Snapshot layout) : Heap × Frame layout :=
  (source.heap.project, source.frame)

inductive Request (layout : Layout) where
  | read (slot : Slot layout)
  | write (slot : Slot layout) (value : Value)
  | fresh (captures : Fin layout.captures → CellId)

inductive Response where
  | read (result : Except Failure Value)
  | write (result : Except Failure Unit)
  | fresh

abbrev Action (layout : Layout) := Request layout × Response

def execute (source : Heap × Frame layout) : Request layout → Response × (Heap × Frame layout)
  | .read slot => (.read (source.2.read source.1 slot), source)
  | .write slot value =>
    match source.2.write source.1 slot value with
    | .ok next => (.write (.ok ()), next)
    | .error failure => (.write (.error failure), source)
  | .fresh captures => (.fresh, Frame.fresh source.1 captures)

namespace Snapshot

def bindCell (source : Snapshot layout) (identity : CellId) (value : Value) :
    Except Failure (Snapshot layout) :=
  match source.heap.write identity value with
  | some heap => .ok { source with heap }
  | none => .error (.danglingCell identity)

def write (source : Snapshot layout) (slot : Slot layout) (value : Value) :
    Except Failure (Snapshot layout) :=
  match slot with
  | .local index =>
    let frame : Frame layout := { source.frame with
      locals := fun slot => if slot = index then some value else source.frame.locals slot }
    .ok { source with frame }
  | .owned index => source.bindCell (source.frame.owned index) value
  | .capture index => source.bindCell (source.frame.captures index) value

def reportWrite (source : Snapshot layout) : Except Failure (Snapshot layout) →
    Response × Snapshot layout
  | .ok next => (.write (.ok ()), next)
  | .error failure => (.write (.error failure), source)

def writeCell (source : Snapshot layout) (identity : CellId) (value : Value) :
    Response × Snapshot layout :=
  reportWrite source (source.bindCell identity value)

def execute (source : Snapshot layout) : Request layout → Response × Snapshot layout
  | .read slot => (.read (source.frame.read source.heap.project slot), source)
  | .write slot value => reportWrite source (source.write slot value)
  | .fresh captures =>
    (.fresh, ⟨source.heap.reserve layout.owned, (Frame.fresh source.heap.project captures).2⟩)

end Snapshot

/-- The request-selected graph of the public store operations. -/
def semantic (layout : Layout) : Cslib.LTS (Heap × Frame layout) (Action layout) :=
  ⟨fun source action target => execute source action.1 = (action.2, target)⟩

def presented (layout : Layout) : Cslib.LTS (Snapshot layout) (Action layout) :=
  ⟨fun source action target => source.execute action.1 = (action.2, target)⟩

end Silmaril.Languages.Python.Core.Closure.Finite
