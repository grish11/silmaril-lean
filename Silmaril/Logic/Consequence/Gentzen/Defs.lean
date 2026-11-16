module

public import Silmaril.Logic.Consequence.Refutation.Defs

/-!
# Gentzen (multiple-conclusion) sequents: structural rules, closures, refutation and tautology

A sequent relation `S : Seq C` reads `S Γ Δ` as "`Γ ⊢ Δ`": premises `Γ`, alternatives `Δ`
(`Seq C` is `List C → List C → Prop`, the same type as a multiple-conclusion system over one
formula carrier). As in `Silmaril.Logic.Consequence.Structural`, every rule is a named property
and closures add exactly the selected rules.

**Rules.**

* `Reflexive S`: a formula shared by `Γ` and `Δ` gives `Γ ⊢ Δ`.
* `WeakensAlong W S`: weaken both sides along the policy `W`. The **default** is list
  inclusion `⊆` on both sides (ordinary weakening: premises and alternatives behave as finite
  sets, so exchange and contraction come with it); order-sensitive policies such as
  `List.Sublist` or `List.Subperm` are opt-in.
* `Cut S`: `Γ ⊢ a :: Δ` and `a :: Γ' ⊢ Δ'` give `Γ ++ Γ' ⊢ Δ ++ Δ'` (contexts concatenated).

`Rules`, `Closed` and the inductive closure `Derives rs S` follow the single-conclusion
versions; `defaultRules` selects reflexivity, `⊆`-weakening and cut.

**Semantics and conversions.** Over `sat : M → C → Prop` (reusing
`Refutation.SatAll`, `Refutation.Unsat`, `Refutation.CheckSound`, `Refutation.CheckComplete`):

* `Valid sat Γ Δ`: every model of all of `Γ` satisfies some member of `Δ`;
  `Taut sat Δ := Valid sat [] Δ` (the disjunction of `Δ` is valid).
* Negation is an explicit function `neg : C → C`, with two separate laws: `NegSound`
  (`m ⊨ neg c → m ⊭ c`) and `NegComplete` (`m ⊭ c → m ⊨ neg c`).
* Raw conversions of a checker: `viaUnsat check neg Γ Δ := check (Γ ++ Δ.map neg)` and
  `viaTauto taut neg Γ Δ := taut (Γ.map neg ++ Δ)`. They are relations, not closures: a sound but
  incomplete checker need not satisfy any structural rule.

`Silmaril.Logic.Consequence.Gentzen.Thms` relates them, with the hypotheses of each direction.
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen

universe u v

variable {C : Type u}

/-- A Gentzen sequent relation: `S Γ Δ` reads `Γ ⊢ Δ`. -/
abbrev Seq (C : Type u) : Type u := List C → List C → Prop

/-! ## Structural rules -/

/-- Reflexivity: a formula shared by both sides gives the sequent. -/
def Reflexive (S : Seq C) : Prop := ∀ ⦃Γ Δ c⦄, c ∈ Γ → c ∈ Δ → S Γ Δ

/-- Weakening of both sides along the policy `W`. -/
def WeakensAlong (W : List C → List C → Prop) (S : Seq C) : Prop :=
  ∀ ⦃Γ Γ' Δ Δ'⦄, W Γ Γ' → W Δ Δ' → S Γ Δ → S Γ' Δ'

/-- Ordinary weakening, the default: along list inclusion on both sides. -/
abbrev WeakSubset (S : Seq C) : Prop := WeakensAlong (fun Γ Δ : List C => Γ ⊆ Δ) S

/-- Cut on one formula, with concatenated contexts. -/
def Cut (S : Seq C) : Prop :=
  ∀ ⦃Γ Γ' Δ Δ' a⦄, S Γ (a :: Δ) → S (a :: Γ') Δ' → S (Γ ++ Γ') (Δ ++ Δ')

/-- Which rules a closure adds. -/
structure Rules (C : Type u) where
  /-- Close under reflexivity. -/
  refl : Prop
  /-- Close under weakening along this policy. -/
  weak : List C → List C → Prop
  /-- Close under cut. -/
  cut : Prop

/-- The default: reflexivity, ordinary (`⊆`) weakening on both sides, and cut. -/
def defaultRules : Rules C := ⟨True, fun Γ Δ => Γ ⊆ Δ, True⟩

/-- Reflexivity, cut, and weakening along an opt-in policy `W`. -/
def withWeakening (W : List C → List C → Prop) : Rules C := ⟨True, W, True⟩

/-- `S` is closed under the selected rules. -/
structure Closed (rs : Rules C) (S : Seq C) : Prop where
  refl : rs.refl → Reflexive S
  weak : WeakensAlong rs.weak S
  cut : rs.cut → Cut S

/-- Derivations from `S` with the selected rules. -/
inductive Derives (rs : Rules C) (S : Seq C) : Seq C
  | base {Γ Δ} : S Γ Δ → Derives rs S Γ Δ
  | refl {Γ Δ c} : rs.refl → c ∈ Γ → c ∈ Δ → Derives rs S Γ Δ
  | weak {Γ Γ' Δ Δ'} : rs.weak Γ Γ' → rs.weak Δ Δ' → Derives rs S Γ Δ → Derives rs S Γ' Δ'
  | cut {Γ Γ' Δ Δ' a} : rs.cut → Derives rs S Γ (a :: Δ) → Derives rs S (a :: Γ') Δ' →
      Derives rs S (Γ ++ Γ') (Δ ++ Δ')

/-! ## Semantics, negation, conversions -/

variable {M : Type v}

/-- Every model of all of `Γ` satisfies some member of `Δ`. -/
def Valid (sat : M → C → Prop) : Seq C := fun Γ Δ =>
  ∀ m, Refutation.SatAll sat m Γ → ∃ d ∈ Δ, sat m d

/-- The disjunction of `Δ` is valid. -/
def Taut (sat : M → C → Prop) (Δ : List C) : Prop := Valid sat [] Δ

/-- A model of `neg c` is not a model of `c`. -/
def NegSound (sat : M → C → Prop) (neg : C → C) : Prop := ∀ m c, sat m (neg c) → ¬ sat m c

/-- A model that is not a model of `c` is a model of `neg c`. -/
def NegComplete (sat : M → C → Prop) (neg : C → C) : Prop := ∀ m c, ¬ sat m c → sat m (neg c)

/-- The checker only accepts lists whose disjunction is valid. -/
def TautSound (sat : M → C → Prop) (taut : List C → Prop) : Prop := ∀ Δ, taut Δ → Taut sat Δ

/-- The checker accepts every list whose disjunction is valid. -/
def TautComplete (sat : M → C → Prop) (taut : List C → Prop) : Prop :=
  ∀ Δ, Taut sat Δ → taut Δ

/-- Raw refutation: `Γ ⊢ Δ` iff `check (Γ ++ [neg d | d ∈ Δ])`. -/
def viaUnsat (check : List C → Prop) (neg : C → C) : Seq C := fun Γ Δ => check (Γ ++ Δ.map neg)

/-- Raw tautology checking: `Γ ⊢ Δ` iff `taut ([neg g | g ∈ Γ] ++ Δ)`. -/
def viaTauto (taut : List C → Prop) (neg : C → C) : Seq C := fun Γ Δ => taut (Γ.map neg ++ Δ)

instance {check : List C → Prop} [DecidablePred check] {neg : C → C} {Γ Δ : List C} :
    Decidable (viaUnsat check neg Γ Δ) := inferInstanceAs (Decidable (check _))

instance {taut : List C → Prop} [DecidablePred taut] {neg : C → C} {Γ Δ : List C} :
    Decidable (viaTauto taut neg Γ Δ) := inferInstanceAs (Decidable (taut _))

end Silmaril.Consequence.Gentzen
