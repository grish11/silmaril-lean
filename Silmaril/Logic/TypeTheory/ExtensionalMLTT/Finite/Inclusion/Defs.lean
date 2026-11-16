module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Defs
public import Silmaril.Logic.SetTheory.Universes.Finite
public import Mathlib.CategoryTheory.Category.Preorder

@[expose] public section

/-! # Inclusions between finite-universe MLTT institutions

A sentence in `MLTT(n)` remains a sentence in `MLTT(m)` when `n ≤ m`.
Models move in the reverse direction by restricting a finite universe supply.
Restriction preserves the total level lookup, giving the satisfaction condition.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.SetTheory

universe u

theorem ETm.UsesBelow.mono {k : ℕ} {t : ETm k} {n m : ℕ}
    (ht : t.UsesBelow n) (hnm : n ≤ m) : t.UsesBelow m :=
  ht.trans hnm

theorem ECtx.UsesBelow.mono {Γ : ECtx} {n m : ℕ}
    (hΓ : Γ.UsesBelow n) (hnm : n ≤ m) : Γ.UsesBelow m :=
  hΓ.trans hnm

theorem EJdg.UsesBelow.mono {j : EJdg} {n m : ℕ}
    (hj : j.UsesBelow n) (hnm : n ≤ m) : j.UsesBelow m :=
  hj.trans hnm

namespace Finite

/-- Include a judgment whose universe occurrences obey a smaller bound. -/
def includeSentence {n m : ℕ} (h : n ≤ m) (j : Sentence n) : Sentence m :=
  ⟨j.val, j.property.mono h⟩

/-- Reducing models forgets the closure laws above the smaller bound. -/
def modelReduct {n m : ℕ} (h : n ≤ m) :
    Discrete (FiniteTower.{u} m) ⥤ Discrete (FiniteTower.{u} n) :=
  Discrete.functor fun T => Discrete.mk (T.restrict h)

/-- Inclusion preserves satisfaction by leaving the term interpretation unchanged. -/
def inclusionCorridor {n m : ℕ} (h : n ≤ m) : room.{u} n ⟶ room.{u} m where
  sen := includeSentence h
  mod := modelReduct h
  sat _ _ := Iff.rfl

/-- The institution inclusion `MLTT(n) → MLTT(m)` for `n ≤ m`. -/
def inclusion {n m : ℕ} (h : n ≤ m) : Inst.CoHom (bundled.{u} n) (bundled.{u} m) where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => inclusionCorridor h

/-- The inclusion adding one available object-language universe. -/
def successor (n : ℕ) : Inst.CoHom (bundled.{u} n) (bundled.{u} (n + 1)) :=
  inclusion (Nat.le_succ n)

/-- Every smaller tower has an expansion agreeing on its available levels.

Only indices below `n` are observable by sentences of `MLTT(n)`. The larger
model may replace the smaller lookup's arbitrary, unconstrained tail. An
extension need not exist in the same ambient Lean carrier.
-/
def ModelsExtend {n m : ℕ} (_h : n ≤ m) : Prop :=
  ∀ T : FiniteTower.{u} n, ∃ T' : FiniteTower.{u} m, ∀ i < n, T'.U i = T.U i

end Finite

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
