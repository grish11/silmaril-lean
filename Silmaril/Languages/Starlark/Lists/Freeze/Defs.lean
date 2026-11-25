module

public import Silmaril.Languages.Starlark.Lists.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists

def Heap.children (heap : Heap) (address : Address) : List Address :=
  match heap[address]? with
  | some cell => cell.contents.children
  | none => []

/-- Reachability among live heap cells, including roots. -/
inductive Reaches (heap : Heap) (roots : List Address) : Address → Prop where
  | root {a : Address} : a < heap.size → a ∈ roots → Reaches heap roots a
  | child {a b : Address} :
      b < heap.size → Reaches heap roots a → b ∈ heap.children a → Reaches heap roots b

/-- A frozen heap preserves the addresses and elements and freezes exactly
the previously frozen cells and the live cells reachable from the roots. -/
structure Freezes (heap : Heap) (roots : List Address) (after : Heap) : Prop where
  size_eq : after.size = heap.size
  cell (a : Address) (before : Cell) (found : heap[a]? = some before) :
    ∃ frozen : Bool, after[a]? = some { before with frozen } ∧
      (frozen = true ↔ before.frozen = true ∨ Reaches heap roots a)

def Heap.canMark (heap : Heap) (roots marked : List Address) (a : Address) : Bool :=
  roots.contains a || marked.any (fun parent => (heap.children parent).contains a)

/-- Saturate the marked set by selecting one eligible, unmarked address at a time. -/
def Heap.mark (heap : Heap) (roots remaining marked : List Address) : List Address :=
  match _found : remaining.find? (heap.canMark roots marked) with
  | none => marked
  | some address => heap.mark roots (remaining.erase address) (address :: marked)
termination_by remaining.length
decreasing_by
  have mem := List.mem_of_find?_eq_some _found
  simp only [List.length_erase_of_mem mem]
  have positive := List.length_pos_of_mem mem
  omega

def Heap.freeze (heap : Heap) (roots : List Address) : Heap :=
  let marked := heap.mark roots (List.range heap.size) []
  heap.mapIdx fun address cell => { cell with frozen := cell.frozen || marked.contains address }

/-- Host operation at the publication boundary. Scalar roots have no outgoing edges. -/
def State.freeze (state : State) (roots : List Value) : State :=
  { state with heap := state.heap.freeze (roots.filterMap Value.address?) }

end Silmaril.Languages.Starlark.Lists
