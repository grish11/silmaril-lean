module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.CellEmbedding.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.CellEmbedding.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.CellEmbedding.Correctness

/-! Exact finite observations for a two-address loop in a larger initialized heap. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress

open RVSDG (Tuple)
open CellEmbedding (Embedding extend restrict SameFrame input result)

variable {small large : Nat} {args : List ValueSort}

theorem Graph.seed_embed (graph : Graph args) (e : Embedding small large) (frame : Heap large)
    (inputs : Tuple (Val small) args) (initial : Heap small) :
    graph.seed (input e inputs) (extend e frame initial) = (graph.seed inputs initial).embed e frame :=
  CellEmbeddingProofs.seed_embed graph e frame inputs initial

/-- Read both feedback operands from the same old bank, with the completed activation heap. -/
theorem Graph.feedback_embed (graph : Graph args) (e : Embedding small large) (frame : Heap large)
    (inputs : Tuple (Val small) args) (header : Header small) (next : Heap small) :
    graph.feedback (input e inputs) (header.embed e frame) (extend e frame next) =
      (graph.feedback inputs header next).embed e frame :=
  CellEmbeddingProofs.feedback_embed graph e frame inputs header next

theorem Graph.step_embed (graph : Graph args) (e : Embedding small large) (frame : Heap large)
    (inputs : Tuple (Val small) args) (header : Header small) :
    graph.step (input e inputs) (header.embed e frame) =
      (graph.step inputs header).map (result e frame) (fun next => next.embed e frame) :=
  CellEmbeddingProofs.step_embed graph e frame inputs header

theorem Graph.evalWithin_embed (graph : Graph args) (e : Embedding small large) (frame : Heap large)
    (inputs : Tuple (Val small) args) (budget : Nat) (header : Header small) :
    graph.evalWithin (input e inputs) budget (header.embed e frame) =
      (graph.evalWithin inputs budget header).map (result e frame) :=
  CellEmbeddingProofs.evalWithin_embed graph e frame inputs budget header

theorem Graph.returns_extend (graph : Graph args) (e : Embedding small large) (frame : Heap large)
    (inputs : Tuple (Val small) args) (initial : Heap small) (word : Word) (final : Heap small) :
    graph.Returns (input e inputs) (extend e frame initial) word (extend e frame final) ↔
      graph.Returns inputs initial word final :=
  CellEmbeddingProofs.returns_extend graph e frame inputs initial word final

/-- At any large initial heap, restrict the final heap to the embedded cells and retain every outside cell. -/
theorem Graph.returns_embed_iff (graph : Graph args) (e : Embedding small large) (inputs : Tuple (Val small) args)
    (initial : Heap large) (word : Word) (final : Heap large) :
    graph.Returns (input e inputs) initial word final ↔
      graph.Returns inputs (restrict e initial) word (restrict e final) ∧ SameFrame e initial final :=
  CellEmbeddingProofs.returns_iff graph e inputs initial word final

theorem Graph.no_return_embed (graph : Graph args) (e : Embedding small large) (inputs : Tuple (Val small) args)
    (initial : Heap large) :
    (∀ word final, ¬ graph.Returns (input e inputs) initial word final) ↔
      ∀ word final, ¬ graph.Returns inputs (restrict e initial) word final :=
  CellEmbeddingProofs.no_return_embed graph e inputs initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress
