module

public import Silmaril.Logic.Consequence.Structural.Defs
public import Silmaril.Logic.Szs.Defs

/-!
# Entailment from UNSAT checks

A satisfaction relation `sat : M → C → Prop` (models `M`, formulas `C`) gives semantic
entailment on lists, `Entails sat Γ c` (every model of all of `Γ` satisfies `c`), and
unsatisfiability of a list, `Unsat sat Γ`. A refutation procedure decides `Γ ⊢ c` by checking
`Γ ++ neg c`, where `neg c` is a *list* of formulas standing for the negation of `c` (one formula
`[¬c]` in a logic with negation; the unit clauses `[[-l] | l ∈ c]` for a CNF clause `c`).

Every hypothesis is a separate, named property, used only where needed
(`Silmaril.Logic.Consequence.Refutation.Thms`):

* negation: `NegSound` (a model of `neg c` is not a model of `c`) and `NegComplete` (a model
  that is not a model of `c` is a model of `neg c`); together, `neg c` is exactly the
  complement of `c`.
* the checker `check : List C → Prop`: `CheckSound` (`check Γ → Unsat Γ`) and `CheckComplete`
  (`Unsat Γ → check Γ`).
* `viaUnsat check neg Γ c := check (Γ ++ neg c)`: the relation a refutation procedure computes.

`Entails sat` is closed under reflexivity, weakening along `⊆` and multi-cut with no
hypothesis. `viaUnsat` is below `Entails` from checker soundness and `NegComplete`, and above
it from checker completeness and `NegSound`; it is therefore cut-closed when all four hold, but
a sound incomplete checker in general is **not** (`Silmaril.Logic.Consequence.Refutation.Examples`).

`problem sat Γ c` is the SZS problem `Γ => c` over models `M` (`Silmaril.Logic.Szs`), relating
`Entails` to `THM` and `Unsat` to `CAX`, in both the 2007 and the current SZS texts.
-/

@[expose] public section

namespace Silmaril.Consequence.Refutation

universe u v

variable {M : Type v} {C : Type u}

/-- `m` satisfies every formula of `Γ`. -/
def SatAll (sat : M → C → Prop) (m : M) (Γ : List C) : Prop := ∀ x ∈ Γ, sat m x

/-- No model satisfies every formula of `Γ`. -/
def Unsat (sat : M → C → Prop) (Γ : List C) : Prop := ∀ m, ¬ SatAll sat m Γ

/-- Semantic entailment: every model of `Γ` is a model of `c`. -/
def Entails (sat : M → C → Prop) : Structural.Rel C := fun Γ c =>
  ∀ m, SatAll sat m Γ → sat m c

/-- A model of `neg c` is not a model of `c`. -/
def NegSound (sat : M → C → Prop) (neg : C → List C) : Prop :=
  ∀ m c, SatAll sat m (neg c) → ¬ sat m c

/-- A model that is not a model of `c` is a model of `neg c`. -/
def NegComplete (sat : M → C → Prop) (neg : C → List C) : Prop :=
  ∀ m c, ¬ sat m c → SatAll sat m (neg c)

/-- The checker only accepts unsatisfiable lists. -/
def CheckSound (sat : M → C → Prop) (check : List C → Prop) : Prop :=
  ∀ Γ, check Γ → Unsat sat Γ

/-- The checker accepts every unsatisfiable list. -/
def CheckComplete (sat : M → C → Prop) (check : List C → Prop) : Prop :=
  ∀ Γ, Unsat sat Γ → check Γ

/-- The consequence relation computed by refutation: `Γ ⊢ c` iff `check (Γ ++ neg c)`. -/
def viaUnsat (check : List C → Prop) (neg : C → List C) : Structural.Rel C := fun Γ c =>
  check (Γ ++ neg c)

/-- The SZS problem `Γ => c`: the models of `Γ` and the models of `c`. -/
def problem (sat : M → C → Prop) (Γ : List C) (c : C) : Logic.Szs.Problem M :=
  ⟨{m | SatAll sat m Γ}, {m | sat m c}⟩

end Silmaril.Consequence.Refutation
