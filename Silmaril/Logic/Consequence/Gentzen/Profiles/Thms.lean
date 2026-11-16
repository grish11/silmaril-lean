module

public import Silmaril.Logic.Consequence.Gentzen.Profiles.Defs
public import Silmaril.Logic.Consequence.Gentzen.Thms
import Silmaril.Proofs.Logic.Consequence.Gentzen.Profiles

/-!
# Gentzen rule profiles: what ordinary weakening gives, and validity

* Ordinary weakening (`WeakSubset`, `⊆` on both sides) gives exchange and contraction on both
  sides (`WeakSubset.exchangeL`, `…exchangeR`, `…contractionL`, `…contractionR`); hence every
  calculus closed under `defaultRules`, and `Valid sat`, has them. Ordered policies do not:
  `…Profiles.Examples.subperm_not_contractionL`.
* Connective rules of `Valid sat`, each from the one direction of the connective's semantic law
  it uses: `valid_conjL` (`m ⊨ a ∧ b → m ⊨ a ∧ m ⊨ b`), `valid_conjR` (the converse),
  `valid_disjL` (`m ⊨ a ∨ b → m ⊨ a ∨ m ⊨ b`), `valid_disjR` (the converse).
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen

universe u v

variable {C : Type u} {S : Seq C}

theorem WeakSubset.exchangeL (h : WeakSubset S) : ExchangeL S :=
  fun _ _ _ hp hd => h hp.subset (fun _ x => x) hd

theorem WeakSubset.exchangeR (h : WeakSubset S) : ExchangeR S :=
  fun _ _ _ hp hd => h (fun _ x => x) hp.subset hd

theorem WeakSubset.contractionL (h : WeakSubset S) : ContractionL S :=
  fun _ _ _ hd => h (by intro x; simp) (fun _ x => x) hd

theorem WeakSubset.contractionR (h : WeakSubset S) : ContractionR S :=
  fun _ _ _ hd => h (fun _ x => x) (by intro x; simp) hd

variable {M : Type v} {sat : M → C → Prop}

theorem valid_conjL {and : C → C → C} (h : ∀ m a b, sat m (and a b) → sat m a ∧ sat m b) :
    ConjL and (Valid sat) :=
  Proofs.Logic.Consequence.Gentzen.Profiles.valid_conjL h

theorem valid_conjR {and : C → C → C} (h : ∀ m a b, sat m a → sat m b → sat m (and a b)) :
    ConjR and (Valid sat) :=
  Proofs.Logic.Consequence.Gentzen.Profiles.valid_conjR h

theorem valid_disjL {or : C → C → C} (h : ∀ m a b, sat m (or a b) → sat m a ∨ sat m b) :
    DisjL or (Valid sat) :=
  Proofs.Logic.Consequence.Gentzen.Profiles.valid_disjL h

theorem valid_disjR {or : C → C → C} (h : ∀ m a b, sat m a ∨ sat m b → sat m (or a b)) :
    DisjR or (Valid sat) :=
  Proofs.Logic.Consequence.Gentzen.Profiles.valid_disjR h

end Silmaril.Consequence.Gentzen
