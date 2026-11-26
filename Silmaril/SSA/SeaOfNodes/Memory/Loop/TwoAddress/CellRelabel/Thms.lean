module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.CellRelabel.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.CellRelabel.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.CellRelabel.Correctness

/-! Cell relabeling preserves the two-address activation and its finite observations. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress

open RVSDG (Tuple)
open CellRelabel (Permutation input heap result)

variable {cells : Nat} {args : List ValueSort}

theorem Graph.seed_relabel (graph : Graph args) (σ : Permutation cells) (inputs : Tuple (Val cells) args)
    (initial : Heap cells) :
    graph.seed (input σ inputs) (heap σ initial) = (graph.seed inputs initial).relabel σ :=
  CellRelabelProofs.seed_relabel graph σ inputs initial

/-- The same old bank supplies both renamed feedback operands. -/
theorem Graph.feedback_relabel (graph : Graph args) (σ : Permutation cells) (inputs : Tuple (Val cells) args)
    (header : Header cells) (next : Heap cells) :
    graph.feedback (input σ inputs) (header.relabel σ) (heap σ next) =
      (graph.feedback inputs header next).relabel σ :=
  CellRelabelProofs.feedback_relabel graph σ inputs header next

theorem Graph.step_relabel (graph : Graph args) (σ : Permutation cells) (inputs : Tuple (Val cells) args)
    (header : Header cells) :
    graph.step (input σ inputs) (header.relabel σ) =
      (graph.step inputs header).map (result σ) (Header.relabel σ) :=
  CellRelabelProofs.step_relabel graph σ inputs header

/-- The same backedge allowance observes the same word and renamed heap. -/
theorem Graph.evalWithin_relabel (graph : Graph args) (σ : Permutation cells) (inputs : Tuple (Val cells) args)
    (budget : Nat) (header : Header cells) :
    graph.evalWithin (input σ inputs) budget (header.relabel σ) =
      (graph.evalWithin inputs budget header).map (result σ) :=
  CellRelabelProofs.evalWithin_relabel graph σ inputs budget header

theorem Graph.returns_relabel (graph : Graph args) (σ : Permutation cells) (inputs : Tuple (Val cells) args)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    graph.Returns (input σ inputs) (heap σ initial) word (heap σ final) ↔
      graph.Returns inputs initial word final :=
  CellRelabelProofs.returns_relabel graph σ inputs initial word final

theorem Graph.no_return_relabel (graph : Graph args) (σ : Permutation cells) (inputs : Tuple (Val cells) args)
    (initial : Heap cells) :
    (∀ word final, ¬ graph.Returns (input σ inputs) (heap σ initial) word final) ↔
      ∀ word final, ¬ graph.Returns inputs initial word final :=
  CellRelabelProofs.no_return_relabel graph σ inputs initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress
