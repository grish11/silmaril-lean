module

public import Silmaril.Logic.Prolog.Horn.Thms

@[expose] public section

namespace Silmaril.Logic.Prolog.Horn

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

namespace Inclusion

def sentence {S : Signature} : Definite.Sentence S → Sentence S
  | .clause c => .clause ⟨c.scope, c.context,
      c.body.map Atom.predicate, some (.predicate c.head)⟩
  | .query q => .query ⟨q.scope, q.context, q.goals.map Atom.predicate⟩

private theorem atoms_holds {S : Signature} {n : Nat} {Γ : Fin n → S.S}
    (M : Model S) (ρ : ∀ i, M.carrier (Γ i)) (atoms : List (Definite.Atom S Γ)) :
    (∀ a ∈ atoms.map Atom.predicate, a.Holds M ρ) ↔
      (∀ a ∈ atoms, a.Holds M ρ) := by
  constructor
  · intro h a ha
    exact h _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
  · intro h a ha
    obtain ⟨original, ho, heq⟩ := List.mem_map.mp ha
    subst a
    exact h original ho

theorem holds {S : Signature} (M : Model S) (s : Definite.Sentence S) :
    (sentence s).Holds M ↔ s.Holds M := by
  cases s with
  | clause c =>
    apply forall_congr'
    intro ρ
    exact imp_congr (atoms_holds M ρ c.body) Iff.rfl
  | query q =>
    apply exists_congr
    intro ρ
    exact atoms_holds M ρ q.goals

theorem sentence_map {S T : Signature} (f : S ⟶ T) (s : Definite.Sentence S) :
    sentence (s.map f) = (sentence s).map f := by
  cases s <;> simp only [sentence, Definite.Sentence.map, Sentence.map,
    Definite.Clause.map, Definite.Query.map, Clause.map, Query.map,
    List.map_map, Option.map_some, Atom.map, Function.comp_def]

end Inclusion

/-- The definite fragment embeds without changing signatures, structures or homomorphisms. -/
def fromDefinite : Inst.CoHom Definite.inst inst where
  Φ := 𝟭 _
  ρ :=
    { app := fun S => ⟨Inclusion.sentence, 𝟭 (FOL.room S).Mod, Inclusion.holds⟩
      naturality := by
        intro S T f
        exact Room.hom_ext (funext (Inclusion.sentence_map f)) rfl }

theorem fromDefinite_modelExpansive : fromDefinite.ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

/-- Inclusion preserves and reflects consequence over every actual FOL model. -/
theorem entails_iff_definite (S : Signature) (H : Set (Definite.Sentence S))
    (s : Definite.Sentence S) :
    (Definite.room S).Entails H s ↔
      (room S).Entails (Inclusion.sentence '' H) (Inclusion.sentence s) :=
  fromDefinite.entails_iff fromDefinite_modelExpansive S H s

end Silmaril.Logic.Prolog.Horn
