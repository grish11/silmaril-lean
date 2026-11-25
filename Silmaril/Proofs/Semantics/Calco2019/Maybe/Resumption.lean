module

public import Silmaril.Semantics.Calco2019.Maybe.LoopDecomposition.Thms
public import Silmaril.Semantics.Calco2019.ExceptionResumption.Specializations

public section

universe u v

namespace Silmaril.Calco2019.Maybe.Proofs

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {P : Coproducts C} [HasInitial C]
  {T : GuardedElgotMonad P} (total : T.IsElgot) {H : C ⥤ C}
  (R : FinalResumptions (Exception.parametrizedElgot T H).toParametrizedMonad)

theorem resumption_freeOn (initial : IsInitial (⟨T, total⟩ : TotalElgot P))
    (S : TotalElgot P) (σ : H ⟶ (S.obj.monad : C ⥤ C)) :
    ∃! k : (⟨(Exception.parametrizedElgot T H).resumptionElgotMonad R,
        Exception.resumption_isElgot T H R total⟩ : TotalElgot P) ⟶ S,
      Exception.suspension T H R ≫ k.hom.hom.toNatTrans = σ := by
  let g : (guardedBimodule P).Hom H S.obj :=
    ⟨σ, GuardedElgotMonad.IsElgot.guardedNatTrans S.property σ⟩
  obtain ⟨k, hk, unique⟩ := Exception.resumption_free R S.obj g (initial.to S).hom
  refine ⟨ObjectProperty.homMk k, ?_, ?_⟩
  · exact ((guardedBimodule_post (Exception.resumptionGenerator R) k).symm.trans
      (congrArg Subtype.val hk.1))
  · intro l hl
    apply ObjectProperty.hom_ext
    apply unique
    constructor
    · apply Subtype.ext
      exact (guardedBimodule_post (Exception.resumptionGenerator R) l.hom).trans hl
    · exact congrArg InducedCategory.Hom.hom
        (initial.hom_ext (ObjectProperty.homMk (Exception.baseEmbedding T H R ≫ l.hom)) (initial.to S))

end Silmaril.Calco2019.Maybe.Proofs
