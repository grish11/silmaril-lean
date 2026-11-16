module

public import Silmaril.Logic.Egglog.Core.Positive.Defs

@[expose] public section

namespace Silmaril.Logic.Egglog.Core.Positive

/-- Equality, predicate and table-row atoms all hold in the singleton model. -/
theorem singletonModel_atom_holds {S : Signature} {n : Nat} {Γ : Fin n → S.S}
    (ρ : ∀ i, (singletonModel S).carrier (Γ i)) (a : Atom S Γ) :
    a.Holds (singletonModel S) ρ := by
  cases a with
  | equal e =>
    change (e.lhs.eval (singletonModel S).toAlgebra ρ : Unit) = _
    exact @Subsingleton.elim Unit inferInstance _ _
  | relation _ _ => exact True.intro
  | row _ _ _ => exact True.intro

/-- Positive rule heads and existential positive queries are always realizable. -/
theorem singletonModel_sentence_holds {S : Signature} (s : Sentence S) :
    s.Holds (singletonModel S) := by
  cases s with
  | rule r => exact fun ρ _ => singletonModel_atom_holds ρ r.head
  | query q => exact ⟨fun _ => (), fun a _ => singletonModel_atom_holds _ a⟩

/-- Every theory of normalized positive Core sentences has an actual Core model.
This includes arbitrary constructor, predicate and custom table signatures. -/
theorem sat_every_theory {S : Signature} (H : Set (Sentence S)) :
    ∃ M : Model S, ∀ s ∈ H, s.Holds M :=
  ⟨singletonModel S, fun s _ => singletonModel_sentence_holds s⟩

end Silmaril.Logic.Egglog.Core.Positive
