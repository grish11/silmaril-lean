module

public import Silmaril.Logic.Consequence.Gentzen.Defs

/-!
# Gentzen rule profiles

Named properties of a sequent relation `S : Seq C`, to be checked one by one (none is assumed by
any other definition). With `Reflexive`, `Cut` and `WeakensAlong` (`…Gentzen.Defs`), core
`MultiSystem.WeakL`/`WeakR`, and `NegL`/`NegR` (`…Gentzen.Calculus.Defs`), they form the
profile of a calculus:

* exchange on each side (`ExchangeL`, `ExchangeR`: permutations) and contraction on each side
  (`ContractionL`, `ContractionR`: a duplicated head formula);
* connective rules for explicit functions `and or : C → C → C` (no connective is assumed of
  `C`): `ConjL`, `ConjR`, `DisjL`, `DisjR`, in the usual sequent-calculus form.
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen

universe u

variable {C : Type u}

/-- Antecedents may be permuted. -/
def ExchangeL (S : Seq C) : Prop := ∀ ⦃Γ Γ' Δ⦄, Γ.Perm Γ' → S Γ Δ → S Γ' Δ

/-- Succedents may be permuted. -/
def ExchangeR (S : Seq C) : Prop := ∀ ⦃Γ Δ Δ'⦄, Δ.Perm Δ' → S Γ Δ → S Γ Δ'

/-- A duplicated head antecedent may be contracted. -/
def ContractionL (S : Seq C) : Prop := ∀ ⦃a Γ Δ⦄, S (a :: a :: Γ) Δ → S (a :: Γ) Δ

/-- A duplicated head succedent may be contracted. -/
def ContractionR (S : Seq C) : Prop := ∀ ⦃Γ a Δ⦄, S Γ (a :: a :: Δ) → S Γ (a :: Δ)

/-- `a, b, Γ ⊢ Δ` gives `a ∧ b, Γ ⊢ Δ`. -/
def ConjL (and : C → C → C) (S : Seq C) : Prop :=
  ∀ ⦃a b Γ Δ⦄, S (a :: b :: Γ) Δ → S (and a b :: Γ) Δ

/-- `Γ ⊢ a, Δ` and `Γ ⊢ b, Δ` give `Γ ⊢ a ∧ b, Δ`. -/
def ConjR (and : C → C → C) (S : Seq C) : Prop :=
  ∀ ⦃a b Γ Δ⦄, S Γ (a :: Δ) → S Γ (b :: Δ) → S Γ (and a b :: Δ)

/-- `a, Γ ⊢ Δ` and `b, Γ ⊢ Δ` give `a ∨ b, Γ ⊢ Δ`. -/
def DisjL (or : C → C → C) (S : Seq C) : Prop :=
  ∀ ⦃a b Γ Δ⦄, S (a :: Γ) Δ → S (b :: Γ) Δ → S (or a b :: Γ) Δ

/-- `Γ ⊢ a, b, Δ` gives `Γ ⊢ a ∨ b, Δ`. -/
def DisjR (or : C → C → C) (S : Seq C) : Prop :=
  ∀ ⦃a b Γ Δ⦄, S Γ (a :: b :: Δ) → S Γ (or a b :: Δ)

end Silmaril.Consequence.Gentzen
