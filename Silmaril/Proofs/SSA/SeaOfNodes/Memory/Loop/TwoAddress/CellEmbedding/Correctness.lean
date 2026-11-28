module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.CellEmbedding.Defs
import Silmaril.SSA.SeaOfNodes.Memory.CellEmbedding.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.CellEmbeddingProofs

open RVSDG (Tuple)
open CellEmbedding (Embedding extend restrict SameFrame input result)

set_option backward.isDefEq.respectTransparency false

variable {small large : Nat} {args : List ValueSort}

private theorem operands_embed (e : Embedding small large) (frame : Heap large) (header : Header small)
    (inputs : Tuple (Val small) args) :
    (header.embed e frame).operands (input e inputs) = input e (header.operands inputs) :=
  rfl

theorem seed_embed (graph : Graph args) (e : Embedding small large) (frame : Heap large)
    (inputs : Tuple (Val small) args) (initial : Heap small) :
    graph.seed (input e inputs) (extend e frame initial) = (graph.seed inputs initial).embed e frame := by
  simp only [Graph.seed, Header.embed, CellEmbedding.input_get, CellEmbedding.value]

theorem feedback_embed (graph : Graph args) (e : Embedding small large) (frame : Heap large)
    (inputs : Tuple (Val small) args) (header : Header small) (next : Heap small) :
    graph.feedback (input e inputs) (header.embed e frame) (extend e frame next) =
      (graph.feedback inputs header next).embed e frame := by
  simp only [Graph.feedback]
  rw [operands_embed, CellEmbedding.input_get, CellEmbedding.input_get]
  rfl

private theorem activation_embed (activation : Loop.Graph args) (e : Embedding small large) (frame : Heap large)
    (inputs : Tuple (Val small) args) (initial : Heap small) :
    activation.step (input e inputs) (extend e frame initial) =
      (activation.step inputs initial).map (result e frame) (extend e frame) := by
  have stop : activation.stopWord (input e inputs) = activation.stopWord inputs :=
    CellEmbedding.input_get e inputs activation.stop
  rw [Loop.Graph.step, Loop.Graph.step, CellEmbedding.denote_graph, stop]
  let out := activation.body.denote inputs initial
  change (if out.1 = activation.stopWord inputs then Sum.inl (β := Heap large) (result e frame out)
    else Sum.inr (extend e frame out.2)) =
      (if out.1 = activation.stopWord inputs then Sum.inl (β := Heap small) out
        else Sum.inr out.2).map (result e frame) (extend e frame)
  by_cases stopped : out.1 = activation.stopWord inputs <;> simp [stopped]

theorem step_embed (graph : Graph args) (e : Embedding small large) (frame : Heap large)
    (inputs : Tuple (Val small) args) (header : Header small) :
    graph.step (input e inputs) (header.embed e frame) =
      (graph.step inputs header).map (result e frame) (fun next => next.embed e frame) := by
  rw [Graph.step, Graph.step, operands_embed]
  change (graph.activation.step (input e (header.operands inputs)) (extend e frame header.heap)).map id _ = _
  rw [activation_embed]
  cases graph.activation.step (header.operands inputs) header.heap with
  | inl _ => rfl
  | inr next => exact congrArg Sum.inr (feedback_embed graph e frame inputs header next)

theorem evalWithin_embed (graph : Graph args) (e : Embedding small large) (frame : Heap large)
    (inputs : Tuple (Val small) args) (budget : Nat) (header : Header small) :
    graph.evalWithin (input e inputs) budget (header.embed e frame) =
      (graph.evalWithin inputs budget header).map (result e frame) := by
  induction budget generalizing header with
  | zero =>
    rw [Graph.evalWithin, Graph.evalWithin, step_embed]
    cases graph.step inputs header <;> rfl
  | succ budget ih =>
    rw [Graph.evalWithin, Graph.evalWithin, step_embed]
    cases graph.step inputs header with
    | inl _ => rfl
    | inr next => exact ih next

theorem returns_extend (graph : Graph args) (e : Embedding small large) (frame : Heap large)
    (inputs : Tuple (Val small) args) (initial : Heap small) (word : Word) (final : Heap small) :
    graph.Returns (input e inputs) (extend e frame initial) word (extend e frame final) ↔
      graph.Returns inputs initial word final := by
  simp only [Graph.Returns, seed_embed, evalWithin_embed]
  apply exists_congr
  intro budget
  rcases graph.evalWithin inputs budget (graph.seed inputs initial) with _ | observed
  · simp
  · simp only [Option.map_some, Option.some.injEq]
    change result e frame observed = result e frame (word, final) ↔ observed = (word, final)
    exact (CellEmbedding.result_injective e frame).eq_iff

theorem returns_iff (graph : Graph args) (e : Embedding small large) (inputs : Tuple (Val small) args)
    (initial : Heap large) (word : Word) (final : Heap large) :
    graph.Returns (input e inputs) initial word final ↔
      graph.Returns inputs (restrict e initial) word (restrict e final) ∧ SameFrame e initial final := by
  constructor
  · rintro ⟨budget, returned⟩
    rw [← CellEmbedding.extend_restrict e initial, seed_embed, evalWithin_embed] at returned
    obtain ⟨⟨observedWord, observedHeap⟩, observed, equal⟩ := Option.map_eq_some_iff.mp returned
    change (observedWord, extend e initial observedHeap) = (word, final) at equal
    have heapEq := congrArg Prod.snd equal
    have wordEq := congrArg Prod.fst equal
    obtain ⟨restrictEq, frameEq⟩ := (CellEmbedding.eq_extend_iff e initial final observedHeap).mp heapEq.symm
    change observedWord = word at wordEq
    subst word
    exact ⟨⟨budget, restrictEq.symm ▸ observed⟩, frameEq⟩
  · rintro ⟨returned, frame⟩
    have finalEq := (CellEmbedding.eq_extend_iff e initial final (restrict e final)).mpr ⟨rfl, frame⟩
    have extended := (returns_extend graph e initial inputs (restrict e initial) word (restrict e final)).mpr returned
    rwa [CellEmbedding.extend_restrict, ← finalEq] at extended

theorem no_return_embed (graph : Graph args) (e : Embedding small large) (inputs : Tuple (Val small) args)
    (initial : Heap large) :
    (∀ word final, ¬ graph.Returns (input e inputs) initial word final) ↔
      ∀ word final, ¬ graph.Returns inputs (restrict e initial) word final := by
  constructor
  · intro absent word final returned
    have extended := (returns_extend graph e initial inputs (restrict e initial) word final).mpr returned
    rw [CellEmbedding.extend_restrict] at extended
    exact absent word (extend e initial final) extended
  · intro absent word final returned
    exact absent word (restrict e final) ((returns_iff graph e inputs initial word final).mp returned).1

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.CellEmbeddingProofs
