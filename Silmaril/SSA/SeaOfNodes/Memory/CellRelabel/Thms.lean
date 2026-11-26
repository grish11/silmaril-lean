module

public import Silmaril.SSA.SeaOfNodes.Memory.CellRelabel.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.CellRelabel.Body

/-! Load, store, and ordered body evaluation commute with cell relabeling. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.CellRelabel

open RVSDG (Port Tuple)

variable {cells : Nat} {args : List ValueSort}

theorem read_heap (σ : Permutation cells) (initial : Heap cells) (a : Address cells) :
    (heap σ initial).read (σ a) = initial.read a :=
  Proofs.read_heap σ initial a

theorem write_heap (σ : Permutation cells) (initial : Heap cells) (a : Address cells) (word : Word) :
    (heap σ initial).write (σ a) word = heap σ (initial.write a word) :=
  Proofs.write_heap σ initial a word

theorem input_get (σ : Permutation cells) (values : Tuple (Val cells) args)
    {sort : ValueSort} (port : Port args sort) :
    (input σ values).get port = value σ sort (values.get port) :=
  Proofs.input_get σ values port

/-- Execute the same ordered body on the renamed inputs and heap. The
word stays the same and the entire final heap moves by the permutation. -/
theorem denote_graph (σ : Permutation cells) (graph : Memory.Graph args)
    (inputs : Tuple (Val cells) args) (initial : Heap cells) :
    graph.denote (input σ inputs) (heap σ initial) = result σ (graph.denote inputs initial) :=
  Proofs.denote_graph σ graph inputs initial

end Silmaril.SSA.SeaOfNodes.Memory.CellRelabel
