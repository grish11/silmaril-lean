module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Institution
public import Silmaril.Logic.Matching.SortMaps.GeneralFixedPoint.Institution
public import Silmaril.Logic.Institution.Morphism

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps
open CategoryTheory Silmaril.Logic.Institution

/-- Forget only the chosen builtin equivalences and their law proofs. Every
actual native homomorphism is retained with the identical map function. -/
def forgetModels (A : Signature) :
    @Model A.bindings A.scope A.literalPrefix A.literals A.hooks ⥤
      Matching.FirstOrder.Model A.scope.signature where
  obj := @Model.native A.bindings A.scope A.literalPrefix A.literals A.hooks
  map h := h
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The actual model-functor square. Eliminating endpoint name equalities
exposes the same native carrier/operation/map data on both routes. -/
theorem forget_reduct {A B : Signature} (f : A ⟶ B) :
    Hom.reductFunctor f ⋙ forgetModels A =
      forgetModels B ⋙ Matching.SortMaps.Hom.reductFunctor f.native := by
  rcases A with ⟨⟨ai, ab, ad⟩, scopeA, prefixA, literalsA, hooksA⟩
  rcases B with ⟨⟨bi, bb, bd⟩, scopeB, prefixB, literalsB, hooksB⟩
  rcases f with ⟨f, hi, hb, labels⟩
  change ((⟨String, scopeA.signature⟩ : Matching.SortMaps.Signature) ⟶
    (⟨String, scopeB.signature⟩ : Matching.SortMaps.Signature)) at f
  change f.sorts ai = bi at hi
  change f.sorts ab = bb at hb
  subst bi
  subst bb
  rfl

/-- Actual natural transformation with identity on full Boolean native
sentences and the genuine forgetful model functor at every scope. -/
def forgetNatural : nativeSignatures ⋙ Matching.SortMaps.generalInstitution ⟶
    nativeInstitution where
  app A := ⟨id, forgetModels A, fun _ _ => Iff.rfl⟩
  naturality := by
    intro A B f
    exact Room.hom_ext rfl (forget_reduct f).symm

/-- An institution morphism (Hom): builtin models forget to native matching
models. The corridor variance is the Hom direction of Morphism.lean. -/
def forgetful : Inst.Hom ⟨Signature, nativeInstitution⟩
    ⟨Matching.SortMaps.Signature, Matching.SortMaps.generalInstitution⟩ :=
  ⟨nativeSignatures, forgetNatural⟩

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps
