module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Typing

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- The original source child-index term, typed under index, shape and position. -/
structure IndexedFormationData (S : Description) (levels : RuleBudget)(n : ℕ) (Γ : Ctx) (H : Set Jdg := ∅)
    extends FormationData S levels n Γ H where
  next : ∀ x ∉ names, ∀ y ∉ insert x names, ∀ p ∉ insert y (insert x names),
    (((Γ.cons x S.index).cons y (S.shape.open x)).cons p ((S.position.open x).open y)).JEqB
      levels H S.index (((S.next.open x).open y).open p) (((S.next.open x).open y).open p)

/-- Preserve the actual source formation and child-index proofs at a larger universe cap. -/
def IndexedFormationData.includeLevels {H : Set Jdg} {S : Description} {levels more : RuleBudget} {n : ℕ} {Γ : Ctx}
    (D : IndexedFormationData S levels n Γ H) (h : levels ≤ more) :
    IndexedFormationData S more n Γ H where
  toFormationData := D.toFormationData.includeLevels h
  next x hx y hy p hp := (D.next x hx y hy p hp).include h

/-- A nonconstant original child index: successor of the source index. -/
def successorDescription : Description := ⟨.nats, .unit, .unit, .succ (.bv 2)⟩

namespace Description

def nextFamily (S : Description) : Tm 0 :=
  .abs S.index (.abs S.shape (.abs S.position S.next))

def nextFamilyType (S : Description) : Tm 0 :=
  .pi S.index (.pi S.shape (.pi S.position (S.index.castLE (by decide))))

/-- The original child-index term compiled by currying and applying to label projections. -/
def compiledChildIndex (S : Description) (label p : Tm 0) : Tm 0 :=
  .app (.app (.app S.nextFamily (.fst label)) (.snd label)) p

end Description

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
