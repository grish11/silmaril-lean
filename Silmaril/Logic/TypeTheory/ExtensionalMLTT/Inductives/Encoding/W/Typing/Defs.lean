module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Terms.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Instantiation
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Head

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- Typed source index, shape and position families, at a common object universe.

This is formation data, not a positivity or indexed-elimination certificate.
The requested child index `next` is not used by raw W formation.
-/
structure FormationData (S : Description) (levels : RuleBudget)(n : ℕ) (Γ : Ctx) (H : Set Jdg := ∅) where
  bound : RuleBudget.Allows levels (n + 1)
  names : Finset String
  declared : Γ.dv ⊆ names
  context : Γ.JEqB levels H .unit .star .star
  index : Γ.JEqB levels H (.univ n) S.index S.index
  shape : ∀ x ∉ names, (Γ.cons x S.index).JEqB levels H (.univ n)
    (S.shape.open x) (S.shape.open x)
  position : ∀ x ∉ names, ∀ y ∉ insert x names,
    ((Γ.cons x S.index).cons y (S.shape.open x)).JEqB levels H (.univ n)
      ((S.position.open x).open y) ((S.position.open x).open y)

/-- The same source formation derivations remain valid with more available universes. -/
def FormationData.includeLevels {H : Set Jdg} {S : Description} {levels more : RuleBudget} {n : ℕ} {Γ : Ctx}
    (D : FormationData S levels n Γ H) (h : levels ≤ more) : FormationData S more n Γ H where
  bound := RuleBudget.Allows.mono h D.bound
  names := D.names
  declared := D.declared
  context := D.context.include h
  index := D.index.include h
  shape x hx := (D.shape x hx).include h
  position x hx y hy := (D.position x hx y hy).include h

/-- One index, one nullary shape: an inhabited source telescope for formation. -/
def nullaryDescription : Description := ⟨.unit, .unit, .empty, .star⟩

namespace Description

def positionFamily (S : Description) : Tm 0 := .abs S.index (.abs S.shape S.position)

def positionFamilyType (S : Description) (n : ℕ) : Tm 0 :=
  .pi S.index (.pi S.shape (.univ n))

/-- Application form of the position family; normal-form agreement is a separate law. -/
def compiledPositions (S : Description) : Tm 1 :=
  .app (.app (S.positionFamily.castLE (by decide)) (.fst (.bv 0))) (.snd (.bv 0))

def compiledRaw (S : Description) : Tm 0 := .wtype S.totalShape S.compiledPositions

/-- Root index by a constant-result W recursor over the compiled carrier. -/
def compiledRoot (S : Description) (t : Tm 0) : Tm 0 :=
  Tm.head S.totalShape S.compiledPositions S.index (.fst (.bv 0)) t

end Description

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
