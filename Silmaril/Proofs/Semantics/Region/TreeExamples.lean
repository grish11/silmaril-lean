module

public import Silmaril.Semantics.Region.Tree.Examples.Defs
public import Silmaril.Semantics.Region.Tree.Thms
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

@[expose] public section
namespace Silmaril.Semantics.Region.Tree.Examples.Proofs

theorem sparse_rooted : sparse.shape.Rooted := by
  refine ⟨rfl, ?_⟩
  intro v
  fin_cases v
  · exact .refl
  · exact .single rfl
  · exact (Relation.ReflTransGen.single (show sparse.shape.Child 0 1 from rfl)).tail rfl

theorem sparse_terminal : sparse.TerminalLeaves := by
  intro v l h c
  fin_cases v
  · cases h
  · cases h
  · fin_cases c <;> unfold Shape.Child <;> decide

theorem sparse_completeLeaves : sparse.CompleteLeaves := by
  intro v terminal
  fin_cases v
  · exact False.elim (terminal 1 rfl)
  · exact False.elim (terminal 2 rfl)
  · exact ⟨2, rfl⟩

theorem sparse_incomplete : ¬ FullyAnnotated sparse := by
  intro h
  obtain ⟨l, eq⟩ := h 1 () none rfl
  cases eq

theorem sparse_contracts : sparse.frontier.child 0 2 := by
  refine ⟨0, 2, rfl, rfl, ?_⟩
  exact Frontier.through (m := 1) (Frontier.child rfl) rfl rfl

theorem anonymous_edge_not_exported : 42 ∈ sparseCFG.successors 1 ∧
    ∀ a, 42 ∉ sparseCFG.flatten.successors a := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  rintro a ⟨v, hv, hb⟩
  have eq : v = (1 : Fin 3) := Fin.ext hb.1
  rw [eq] at hv
  cases hv

end Silmaril.Semantics.Region.Tree.Examples.Proofs
