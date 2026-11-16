module

public import Silmaril.Logic.Consequence.Structural.Defs
public import Mathlib.Data.Finset.Dedup

/-!
# From list sequents to finite sets and sets of premises

A list-sequent relation `R : Rel C` induces relations on `Finset C` and on `Set C`:

* `onFinset R s c := R s.toList c`. `Finset.toList` picks *some* enumeration of `s`, so this
  is canonical only when `R` cannot tell lists with the same members apart: weakening along
  `⊆` (`WeakSubset`) is exactly the assumption used (`…Finitary.Thms`: `onFinset_toFinset`).
* `onSet R S c`: some finite list of members of `S` yields `c` (the compact, finitary reading).
  `cn R S` is the set of such `c`. It is monotone for every `R`, extensive (`S ⊆ cn R S`) when
  `R` is reflexive, and idempotent (`cn R (cn R S) ⊆ cn R S`) when `R` is cut-closed: no
  weakening is needed, since `onSet` already lets `Γ` be any list of members. `cnClosure` packages it as a Mathlib `ClosureOperator (Set C)`.

Future extension (not done here): premises in a preorder or a lattice of theories, with
weakening along its order, would replace `⊆` on lists by the order and `List.flatMap` in cut by
a join.
-/

@[expose] public section

namespace Silmaril.Consequence.Structural

universe u

variable {C : Type u}

/-- `R` on finite sets of premises, through an enumeration of the set. -/
noncomputable def onFinset (R : Rel C) (s : Finset C) (c : C) : Prop := R s.toList c

/-- `R` on arbitrary sets of premises: some finite list of members yields `c`. -/
def onSet (R : Rel C) (S : Set C) (c : C) : Prop := ∃ Γ : List C, (∀ x ∈ Γ, x ∈ S) ∧ R Γ c

/-- The consequences of a set of premises. -/
def cn (R : Rel C) (S : Set C) : Set C := {c | onSet R S c}

end Silmaril.Consequence.Structural
