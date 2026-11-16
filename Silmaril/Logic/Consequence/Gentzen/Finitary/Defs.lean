module

public import Silmaril.Logic.Consequence.Gentzen.Thms
public import Mathlib.Data.Finset.Dedup

/-!
# Gentzen sequents with finite sets and sets on both sides

* `onFinset S s t := S s.toList t.toList`. `Finset.toList` picks some enumeration, so this is
  canonical only when `S` cannot tell apart lists with the same members: ordinary weakening on
  both sides (`WeakSubset`) is the assumption used (`…Finitary.Thms`).
* `onSet S A B`: some finite lists of members of `A` and of `B` form a sequent of `S`. This is
  the *finitary* reading. For semantic validity it is sound for the infinitary reading "every
  model of all of `A` satisfies some member of `B`" (`InfValid`), but the converse is compactness
  and is not assumed: it fails for a non-compact satisfaction relation
  (`…Finitary.Examples.not_onSet_valid`).
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen

universe u v

variable {C : Type u}

/-- `S` on finite sets, through enumerations of both sides. -/
noncomputable def onFinset (S : Seq C) (s t : Finset C) : Prop := S s.toList t.toList

/-- `S` on sets: some finite lists of members of each side form a sequent. -/
def onSet (S : Seq C) (A B : Set C) : Prop :=
  ∃ Γ Δ : List C, (∀ x ∈ Γ, x ∈ A) ∧ (∀ x ∈ Δ, x ∈ B) ∧ S Γ Δ

/-- Infinitary validity: every model of all of `A` satisfies some member of `B`. -/
def InfValid {M : Type v} (sat : M → C → Prop) (A B : Set C) : Prop :=
  ∀ m, (∀ a ∈ A, sat m a) → ∃ b ∈ B, sat m b

end Silmaril.Consequence.Gentzen
