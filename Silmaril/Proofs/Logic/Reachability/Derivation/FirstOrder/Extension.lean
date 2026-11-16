module

public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Stock.Extension.Defs

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder
open Silmaril.Logic.Institution.Examples
variable {Sg : FOL.Signature}
namespace Embedding

private theorem dependent_congr {α : Type} {β : α → Type} (f : (x : α) → β x)
    {x y : α} (h : x = y) : HEq (f x) (f y) := by
  cases h
  rfl

/-- Exact projection is proved using name injectivity and the actual sort cast. -/
theorem assignment_extendLocal {k : Nat} {Γ : Fin k → Sg.S}
    (e : Embedding Γ) (M : FOL.Structure Sg) (defaults : (s : Sg.S) → M.carrier s)
    (a : (i : Fin k) → M.carrier (Γ i)) :
    e.assignment M (e.extendLocal M defaults a) = a := by
  classical
  funext i
  unfold assignment extendLocal
  have hex : ∃ j : Fin k, e.name j = e.name i := ⟨i, rfl⟩
  rw [dite_eq_left hex]
  have same : Classical.choose hex = i := e.name_injective (Classical.choose_spec hex)
  apply eq_of_heq
  exact (cast_heq _ _).trans (dependent_congr a same)

/-- The construction uses precisely the specified defaults away from the finite
embedded range, without assuming any additional stock representation laws. -/
theorem extendLocal_outside {k : Nat} {Γ : Fin k → Sg.S}
    (e : Embedding Γ) (M : FOL.Structure Sg) (defaults : (s : Sg.S) → M.carrier s)
    (a : (i : Fin k) → M.carrier (Γ i)) (j : StockName Sg)
    (outside : j ∉ Set.range e.name) : e.extendLocal M defaults a j = defaults j.1 := by
  classical
  unfold extendLocal
  exact dite_eq_right outside

end Embedding
end Silmaril.Logic.Reachability.Derivation.FirstOrder
