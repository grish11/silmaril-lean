module

public import Silmaril.Logic.TypeTheory.LambdaPi.Category.Thms
public import Silmaril.Logic.Institution.Syntactic.Thms
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section

/-!
# A functor from λΠ-modulo presentations to institutions

The models here are closed judgment theories. This provides a syntactic Hets
connection and exact satisfaction condition. Concrete normalization, semantic
soundness and consistency are separate obligations for admissible presentations.
-/

namespace Silmaril.Logic.TypeTheory.LambdaPi

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory

noncomputable section

/-- Each presentation is assigned its closed-theory institution, functorially. -/
def calculusToInstitutions : Calculus ⥤ CoIns.{0,0,0,0,0} :=
  calculusToEntailment ⋙ Silmaril.Logic.Institution.Syntactic.toInstitutions

/-- The actual inference rules paired with closed-theory semantics. -/
def Calculus.logic (C : Calculus) : LogicalSystem.{0,0,0,0,0} (Discrete Unit) where
  I := (Functor.const (Discrete Unit)).obj
    (Silmaril.Logic.Institution.Syntactic.room C.entailment)
  Derives _ H J := Derives C H J
  refl _ J := .hyp (Set.mem_singleton J)
  mono := by
    intro S H H' J hsub h
    exact h.mono hsub
  trans := by
    intro S H Δ J hΔ h
    exact h.bind fun K hK => Or.elim hK Derives.hyp (hΔ K)
  map_derives := by
    intro S T σ H J h
    change Set Judgment at H
    change Judgment at J
    change Derives C ((fun K : Judgment => K) '' H) J
    exact Derives.mono (H := H) (K := (fun K : Judgment => K) '' H)
      (fun K hK => ⟨K, hK, rfl⟩) h

/-- Every structural calculus map is a Hets logic-translation edge. -/
def hets : LogicGraph.{0,0,0,0,0,0,0} where
  Logics := Calculus
  inst := calculusToInstitutions.obj
  Comor C D := C ⟶ D
  comor := calculusToInstitutions.map
  Mor _ _ := PEmpty
  mor e := e.elim

end
end Silmaril.Logic.TypeTheory.LambdaPi
