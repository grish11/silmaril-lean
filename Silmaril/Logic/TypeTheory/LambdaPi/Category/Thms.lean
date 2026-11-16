module

public import Silmaril.Logic.TypeTheory.LambdaPi.Category.Defs
public import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.Category

@[expose] public section

namespace Silmaril.Logic.TypeTheory.LambdaPi

open CategoryTheory Silmaril.Logic.Institution.Metatheory
open Silmaril.Proofs.Logic.TypeTheory.LambdaPi

@[ext] theorem Morphism.ext {C D : Calculus} {F G : Morphism C D}
    (h : F.constants = G.constants) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Actual declaration/rewrite-preserving translations form a category. -/
instance : Category Calculus where
  Hom := Morphism
  id _ :=
    { constants := id
      declared := fun h => by simpa only [map_id, id_eq] using h
      rules := fun r h => by simpa only [rule_map_id] using h }
  comp F G :=
    { constants := G.constants ∘ F.constants
      declared := fun h => by simpa only [map_comp, Function.comp_apply] using G.declared (F.declared h)
      rules := fun r h => by simpa only [rule_map_comp] using G.rules _ (F.rules r h) }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Every structural translation preserves the full hypothetical typing rules. -/
theorem Morphism.map_derives {C D : Calculus} (F : C ⟶ D) {H : Set Judgment} {J : Judgment}
    (h : Derives C H J) :
    Derives D (Judgment.mapConstants F.constants '' H) (J.mapConstants F.constants) :=
  derives_map F h

/-- The actual typing calculus, as a Tarskian entailment relation. -/
def Calculus.entailment (C : Calculus) : ER where
  Sen := Judgment
  Derives := Derives C
  refl J := .hyp (Set.mem_singleton J)
  mono h hk := hk.mono h
  trans hΔ h := h.bind fun J hJ => Or.elim hJ Derives.hyp (hΔ J)

/-- Forgetting syntax translations gives a functor to entailment relations. -/
def calculusToEntailment : Calculus ⥤ ER where
  obj := Calculus.entailment
  map F := ⟨Judgment.mapConstants F.constants, F.map_derives⟩
  map_id _ := by
    apply ER.hom_ext
    funext J
    exact judgment_map_id J
  map_comp F G := by
    apply ER.hom_ext
    funext J
    exact judgment_map_comp F.constants G.constants J

end Silmaril.Logic.TypeTheory.LambdaPi
