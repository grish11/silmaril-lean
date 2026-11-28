module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.CellRelabel.Defs
import Silmaril.SSA.SeaOfNodes.Memory.CellRelabel.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.CellRelabelProofs

open RVSDG (Tuple)
open CellRelabel (Permutation input heap result)

set_option backward.isDefEq.respectTransparency false

variable {cells : Nat} {args : List ValueSort}

private theorem operands_relabel (σ : Permutation cells) (header : Header cells) (inputs : Tuple (Val cells) args) :
    (header.relabel σ).operands (input σ inputs) = input σ (header.operands inputs) :=
  rfl

theorem seed_relabel (graph : Graph args) (σ : Permutation cells) (inputs : Tuple (Val cells) args)
    (initial : Heap cells) :
    graph.seed (input σ inputs) (heap σ initial) = (graph.seed inputs initial).relabel σ := by
  simp only [Graph.seed, Header.relabel, CellRelabel.input_get, CellRelabel.value]

theorem feedback_relabel (graph : Graph args) (σ : Permutation cells) (inputs : Tuple (Val cells) args)
    (header : Header cells) (next : Heap cells) :
    graph.feedback (input σ inputs) (header.relabel σ) (heap σ next) =
      (graph.feedback inputs header next).relabel σ := by
  simp only [Graph.feedback]
  rw [operands_relabel, CellRelabel.input_get, CellRelabel.input_get]
  rfl

private theorem activation_relabel (activation : Loop.Graph args) (σ : Permutation cells)
    (inputs : Tuple (Val cells) args) (initial : Heap cells) :
    activation.step (input σ inputs) (heap σ initial) =
      (activation.step inputs initial).map (result σ) (heap σ) := by
  have stop : activation.stopWord (input σ inputs) = activation.stopWord inputs :=
    CellRelabel.input_get σ inputs activation.stop
  rw [Loop.Graph.step, Loop.Graph.step, CellRelabel.denote_graph, stop]
  let out := activation.body.denote inputs initial
  change (if out.1 = activation.stopWord inputs then Sum.inl (β := Heap cells) (result σ out)
    else Sum.inr (heap σ out.2)) =
      (if out.1 = activation.stopWord inputs then Sum.inl (β := Heap cells) out
        else Sum.inr out.2).map (result σ) (heap σ)
  by_cases stopped : out.1 = activation.stopWord inputs <;> simp [stopped]

theorem step_relabel (graph : Graph args) (σ : Permutation cells) (inputs : Tuple (Val cells) args)
    (header : Header cells) :
    graph.step (input σ inputs) (header.relabel σ) =
      (graph.step inputs header).map (result σ) (Header.relabel σ) := by
  rw [Graph.step, Graph.step, operands_relabel]
  change (graph.activation.step (input σ (header.operands inputs)) (heap σ header.heap)).map id _ = _
  rw [activation_relabel]
  cases graph.activation.step (header.operands inputs) header.heap with
  | inl _ => rfl
  | inr next => exact congrArg Sum.inr (feedback_relabel graph σ inputs header next)

theorem evalWithin_relabel (graph : Graph args) (σ : Permutation cells) (inputs : Tuple (Val cells) args)
    (budget : Nat) (header : Header cells) :
    graph.evalWithin (input σ inputs) budget (header.relabel σ) =
      (graph.evalWithin inputs budget header).map (result σ) := by
  induction budget generalizing header with
  | zero =>
    rw [Graph.evalWithin, Graph.evalWithin, step_relabel]
    cases graph.step inputs header <;> rfl
  | succ budget ih =>
    rw [Graph.evalWithin, Graph.evalWithin, step_relabel]
    cases graph.step inputs header with
    | inl _ => rfl
    | inr next => exact ih next

theorem returns_relabel (graph : Graph args) (σ : Permutation cells) (inputs : Tuple (Val cells) args)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    graph.Returns (input σ inputs) (heap σ initial) word (heap σ final) ↔
      graph.Returns inputs initial word final := by
  simp only [Graph.Returns, seed_relabel, evalWithin_relabel]
  apply exists_congr
  intro budget
  rcases graph.evalWithin inputs budget (graph.seed inputs initial) with _ | observed
  · simp
  · simp only [Option.map_some, Option.some.injEq]
    change result σ observed = result σ (word, final) ↔ observed = (word, final)
    exact (result σ).injective.eq_iff

theorem no_return_relabel (graph : Graph args) (σ : Permutation cells) (inputs : Tuple (Val cells) args)
    (initial : Heap cells) :
    (∀ word final, ¬ graph.Returns (input σ inputs) (heap σ initial) word final) ↔
      ∀ word final, ¬ graph.Returns inputs initial word final := by
  constructor
  · intro missing word final returned
    exact missing word (heap σ final) ((returns_relabel graph σ inputs initial word final).mpr returned)
  · intro missing word final
    obtain ⟨old, rfl⟩ := (heap σ).surjective final
    exact fun returned => missing word old ((returns_relabel graph σ inputs initial word old).mp returned)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.CellRelabelProofs
