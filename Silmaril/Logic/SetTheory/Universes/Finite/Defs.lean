module

public import Silmaril.Logic.SetTheory.Universes.Defs

@[expose] public section

/-!
# Finite supplies of set universes

`FiniteTower n` specifies exactly the first `n` Grothendieck universes and their
successor memberships. Its total lookup function makes it usable by syntax
whose levels are natural numbers; entries outside the bound carry no laws.

`HasFiniteTower n` requests a model supply in one specified Lean set carrier.
It does not request towers of every height in that carrier.
-/

namespace Silmaril.Logic.SetTheory

universe u

/-- A universe hierarchy with closure laws only below the finite bound `n`. -/
structure FiniteTower (n : ℕ) : Type (u + 1) where
  /-- Level lookup; only indices below `n` are constrained. -/
  U : ℕ → ZFSet.{u}
  /-- Every in-range level is a Grothendieck universe. -/
  isGrothendieck : ∀ i < n, IsGrothendieckUniverse (U i)
  /-- Each level belongs to the next when both levels are in range. -/
  mem_succ : ∀ i, i + 1 < n → U i ∈ U (i + 1)

/-- A finite tower is available in this specified Lean universe. -/
class HasFiniteTower (n : ℕ) : Prop where
  /-- Model existence, independent of any type-theory soundness claim. -/
  nonempty : Nonempty (FiniteTower.{u} n)

/-- Select a supplied finite tower. -/
noncomputable def HasFiniteTower.tower (n : ℕ) [HasFiniteTower.{u} n] : FiniteTower.{u} n :=
  Classical.choice (HasFiniteTower.nonempty (n := n))

end Silmaril.Logic.SetTheory
