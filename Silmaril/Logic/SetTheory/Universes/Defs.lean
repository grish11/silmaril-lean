module

public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.ZFC.VonNeumann
public import Silmaril.Logic.SetTheory.Nat

@[expose] public section

/-!
# Set universes

A Grothendieck universe is transitive, contains the natural numbers, and is
closed under pairs, powersets and unions indexed by its members. The lifting
construction embeds the sets of one Lean universe in a larger one.

Adapted from internal Silmaril at 288ee492ad09224b78ac44f8456e2ffcd6482384,
Logic/SetTheory/Universe.lean. The closure model does not assume the
Tarski-Grothendieck axiom or the existence of an infinite tower.
-/

namespace Silmaril.Logic.SetTheory

universe u v

open ZFSet

/-- Closure properties of a Grothendieck universe containing omega. -/
structure IsGrothendieckUniverse (U : ZFSet.{u}) : Prop where
  isTransitive : U.IsTransitive
  pair_mem : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U
  powerset_mem : ∀ x ∈ U, powerset x ∈ U
  iUnion_mem : ∀ x ∈ U, ∀ f : x → ZFSet.{u}, (∀ i, f i ∈ U) → (⋃ i, f i) ∈ U
  omega_mem : omega ∈ U

/-- Embed a set in a carrier whose Lean universe is at least as large. -/
noncomputable def liftSet (x : ZFSet.{u}) : ZFSet.{max u v} :=
  haveI : Small.{max u v} x := small_lift.{u + 1, v, u} x
  range fun y : x => liftSet y.1
termination_by x
decreasing_by exact y.2

/-- The set containing the lifts of all sets from the lower Lean universe. -/
noncomputable def universeSet : ZFSet.{u + 1} := range liftSet.{u, u + 1}

end Silmaril.Logic.SetTheory
