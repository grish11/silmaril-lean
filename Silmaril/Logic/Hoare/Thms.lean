module

public import Silmaril.Proofs.Logic.Hoare.Phases
public import Silmaril.Proofs.Logic.Hoare.Naturality

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Hoare
open CategoryTheory Silmaril.Logic.Institution
variable (C : Type) {A B D : Signature C}

theorem Triple.map_id (t : Triple C A) : t.map C (𝟙 A) = t := by
  cases t with
  | mk c p q =>
      change Triple.mk c (p.map (𝟙 A.language)) (q.map (𝟙 A.language)) = _
      rw [PDL.Formula.map_id, PDL.Formula.map_id]

theorem Triple.map_comp (f : A ⟶ B) (g : B ⟶ D) (t : Triple C A) :
    t.map C (f ≫ g) = (t.map C f).map C g := by
  cases t with
  | mk c p q =>
      change Triple.mk c (p.map (f.language ≫ g.language)) (q.map (f.language ≫ g.language)) = _
      rw [PDL.Formula.map_comp, PDL.Formula.map_comp]
      rfl

theorem Triple.satisfaction (f : A ⟶ B) (M : Model C B) (t : Triple C A) :
    (t.map C f).Satisfies C M ↔ t.Satisfies C (ModalMu.reduct f.language M) := by
  simp only [Triple.Satisfies, Triple.map, PDL.Formula.holds_map, ← body_reduct f M]
  rfl

def institution : Signature C ⥤ Room where
  obj A := ⟨Triple C A, Cat.of (Model C A), Triple.Satisfies C⟩
  map f := ⟨Triple.map C f, ModalMu.modelReduct f.language, Triple.satisfaction C f⟩
  map_id _ := Room.hom_ext (funext (Triple.map_id C)) rfl
  map_comp f g := Room.hom_ext (funext (Triple.map_comp C f g)) rfl

/-- `institution` as a bundled `Inst`, named so that records and comorphisms can refer to it. -/
def inst := (⟨Signature C, institution C⟩ : Silmaril.Logic.Institution.Inst)

/-- Actual reachability sentences on the canonically phased models. No truth constraints are stored. -/
def canonicalInstitution : Signature C ⥤ Room where
  obj A := ⟨Reachability.Sentence () (reachSignaturesObj C A), Cat.of (Model C A),
    fun M p => Reachability.Sentence.Satisfies () (expand C M) p⟩
  map f := ⟨Reachability.Sentence.map () (reachSignaturesMap C f), ModalMu.modelReduct f.language, by
    intro M p
    change Reachability.Sentence.Satisfies () (expand C M) (p.map () (reachSignaturesMap C f)) ↔
      Reachability.Sentence.Satisfies () (expand C (ModalMu.reduct f.language M)) p
    rw [Reachability.Sentence.satisfaction, expand_reduct]⟩
  map_id A := by
    apply Room.hom_ext
    · funext p
      have hf : reachSignaturesMap C (𝟙 A) = 𝟙 (reachSignaturesObj C A) :=
        (reachSignatures C).map_id A
      exact (congrArg (fun f => p.map () f) hf).trans (Reachability.Sentence.map_id () p)
    · rfl
  map_comp f g := by
    apply Room.hom_ext
    · funext p
      have hf : reachSignaturesMap C (f ≫ g) = reachSignaturesMap C f ≫ reachSignaturesMap C g :=
        (reachSignatures C).map_comp f g
      exact (congrArg (fun h => p.map () h) hf).trans
        (Reachability.Sentence.map_comp () (reachSignaturesMap C f) (reachSignaturesMap C g) p)
    · rfl

/-- `canonicalInstitution` as a bundled `Inst`, named so that records and comorphisms can refer to it. -/
def canonicalInst := (⟨Signature C, canonicalInstitution C⟩ : Silmaril.Logic.Institution.Inst)

def canonicalNatural : institution C ⟶ (𝟭 (Signature C)) ⋙ canonicalInstitution C where
  app A := ⟨encode C, 𝟭 (Model C A), encode_correct⟩
  naturality := by
    intro A B f
    exact Room.hom_ext (funext (encode_map f)) rfl

def toCanonicalReachability : Inst.CoHom ⟨Signature C, institution C⟩
    ⟨Signature C, canonicalInstitution C⟩ := ⟨𝟭 _, canonicalNatural C⟩

theorem toCanonicalReachability_modelExpansive : (toCanonicalReachability C).ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

theorem entails_iff (A : Signature C) (H : Set (Triple C A)) (t : Triple C A) :
    ((institution C).obj A).Entails H t ↔
      ((canonicalInstitution C).obj A).Entails (encode C '' H) (encode C t) :=
  (toCanonicalReachability C).entails_iff (toCanonicalReachability_modelExpansive C) A H t

def canonicalModels (A : Signature C) : Model C A ⥤ Reachability.Model () (reachSignaturesObj C A) where
  obj := expand C
  map h := eqToHom (congrArg (expand C) h.down)

private theorem hom_hext {X : Algebraic.ManySorted.Signature Unit}
    {M M' N N' : Matching.FirstOrder.Model X} (hM : M = M') (hN : N = N')
    (f : Matching.FirstOrder.Model.Hom M N) (g : Matching.FirstOrder.Model.Hom M' N')
    (h : HEq f.map g.map) : HEq f g := by
  cases hM; cases hN
  exact heq_of_eq (Matching.FirstOrder.Model.Hom.ext _ _ (eq_of_heq h))

theorem canonicalModels_natural (f : A ⟶ B) :
    canonicalModels C B ⋙ Matching.FirstOrder.SignatureMap.reductFunctor (reachSignaturesMap C f).algebra =
      ModalMu.modelReduct f.language ⋙ canonicalModels C A := by
  apply Functor.hext (expand_reduct f)
  intro M N h
  apply hom_hext (expand_reduct f M) (expand_reduct f N)
  cases h with
  | up he =>
      cases he
      rfl

/-- Restriction from arbitrary reachability models to the actual canonical phase shape. -/
def restrictionNatural : (reachSignatures C ⋙ Reachability.institution ()) ⟶ canonicalInstitution C where
  app A := ⟨id, canonicalModels C A, fun _ _ => Iff.rfl⟩
  naturality := by
    intro A B f
    exact Room.hom_ext rfl (canonicalModels_natural C f)

def restrictReachability : Inst.CoHom ⟨Signature C, reachSignatures C ⋙ Reachability.institution ()⟩
    ⟨Signature C, canonicalInstitution C⟩ := ⟨𝟭 _, restrictionNatural C⟩

end Silmaril.Logic.Hoare
