module

public import Silmaril.Games.Abstract.StratOps.Thms
public import Mathlib.Logic.Equiv.Defs

/-!
# The canonical play objects as a category

A strategy `σ : DStrategy E (funSig S A B)` is **realizable** when it is the play object of its
own readback, `toDStrat (readback σ) = σ` (`StratOps.Realizable`). The realizable strategies
are exactly the play objects `toDStrat t` of triples, and of admissible triples
(`StratOps.realizable_iff`, `StratOps.realizable_iff_adm`).

`CanonStrat E S A B` is the subtype of realizable strategies. It is represented by the
admissible triples (`CanonStrat.equivAdm : CanonStrat E S A B ≃ AdmTriple E S A B`, readback
one way and `toDStrat` the other); `CanonStrat.rep σ = readback σ.1` is the admissible
representative.

The operations (`seq`, `pure`, `map`, `comap`, `whiskerRight`, `whiskerLeft`, `case`, `iter`)
are the game-level operations `seqD`, … of `Silmaril.Games.Abstract.StratOps`. Each is a
`toDStrat`, so it is realizable whatever its arguments; on `CanonStrat` the laws hold with no
hypothesis (`Silmaril.Games.Abstract.CanonStrat.Thms`).

**Scope.** The domain of the laws is `CanonStrat`. General prefix-closed (divergence-observing)
strategies on `funSig S A B` are *not* claimed to satisfy them: such a strategy may have plays
that no triple produces (for example a play that depends on earlier rounds), and readback, used
by the game-level operations, forgets them.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A B C : Type u}

namespace StratOps

/-- **A realizable strategy**: the play object of its own readback. -/
def Realizable (σ : DStrategy E (funSig S A B)) : Prop := toDStrat (readback σ) = σ

/-- Every play object is realizable. -/
theorem realizable_toDStrat (t : ObsTriple E S A B) : Realizable (toDStrat t) := by
  rw [Realizable, readback_toDStrat, toDStrat_sat]

end StratOps

/-- **The canonical play objects**: the realizable strategies on the function interface. -/
abbrev CanonStrat (E : Sig.{u}) (S A B : Type u) : Type u :=
  {σ : DStrategy E (funSig S A B) // StratOps.Realizable σ}

namespace CanonStrat

/-- The canonical play object of a triple. -/
def toCanon (t : ObsTriple E S A B) : CanonStrat E S A B := ⟨toDStrat t, realizable_toDStrat t⟩

/-- The representative triple: the readback. -/
def rep (σ : CanonStrat E S A B) : ObsTriple E S A B := readback σ.1

/-- The representative is admissible. -/
theorem admissible_rep (σ : CanonStrat E S A B) : Admissible (rep σ) := by
  have h := readback_toDStrat (readback σ.1)
  rw [σ.2] at h
  exact h.symm

/-- **Representation** by admissible triples: readback and `toDStrat`. -/
def equivAdm : CanonStrat E S A B ≃ AdmTriple E S A B where
  toFun σ := ⟨rep σ, admissible_rep σ⟩
  invFun t := toCanon t.1
  left_inv σ := Subtype.ext σ.2
  right_inv t := Subtype.ext (readback_toDStrat_adm t.2)

/-! ## Operations -/

/-- Sequencing. -/
def seq (σ : CanonStrat E S A B) (τ : CanonStrat E S B C) : CanonStrat E S A C :=
  ⟨seqD σ.1 τ.1, realizable_toDStrat _⟩

/-- The identity. -/
def pure : CanonStrat E S A A := ⟨pureD, realizable_toDStrat _⟩

/-- Post-composition with a pure function. -/
def map (σ : CanonStrat E S A B) (h : B → C) : CanonStrat E S A C :=
  ⟨mapD σ.1 h, realizable_toDStrat _⟩

/-- Pre-composition with a pure function. -/
def comap {A' : Type u} (σ : CanonStrat E S A B) (k : A' → A) : CanonStrat E S A' B :=
  ⟨comapD σ.1 k, realizable_toDStrat _⟩

/-- Right whiskering `σ ⋉ C`. -/
def whiskerRight (σ : CanonStrat E S A B) (C : Type u) : CanonStrat E S (A × C) (B × C) :=
  ⟨whiskerRightD σ.1 C, realizable_toDStrat _⟩

/-- Left whiskering `C ⋊ σ`. -/
def whiskerLeft (C : Type u) (σ : CanonStrat E S A B) : CanonStrat E S (C × A) (C × B) :=
  ⟨whiskerLeftD C σ.1, realizable_toDStrat _⟩

/-- Copairing. -/
def case (σ : CanonStrat E S A C) (τ : CanonStrat E S B C) : CanonStrat E S (A ⊕ B) C :=
  ⟨caseD σ.1 τ.1, realizable_toDStrat _⟩

/-- Iteration (`inl` exits, `inr` continues). -/
def iter (σ : CanonStrat E S A (B ⊕ A)) : CanonStrat E S A B :=
  ⟨iterD σ.1, realizable_toDStrat _⟩

end CanonStrat

end Silmaril.Games.Abstract
