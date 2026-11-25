module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Free.Defs
import Silmaril.Semantics.Calco2019.ExceptionResumption.Interpretation.Iteration
import Silmaril.Semantics.Calco2019.ExceptionResumption.Interpretation.Uniqueness
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory CategoryTheory.Limits Exception

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [HasInitial C] {P : Coproducts C}
  {T : GuardedElgotMonad P} {H : C ⥤ C}
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)

theorem resumption_free :
    (guardedBimodule P).IsFreeExtension (resumptionGenerator R) (baseEmbedding T H R) := by
  intro S σ ξ
  let m := mediatorHom R ξ σ
  refine ⟨m, ⟨?_, ?_⟩, ?_⟩
  · apply Subtype.ext
    rw [guardedBimodule_post]
    apply NatTrans.ext
    funext X
    change (suspension T H R).app X ≫ m.hom.app X = σ.val.app X
    rw [suspension_app, mediatorHom_app]
    exact (pure_comp_of S.monad _ _).symm.trans (congrArg Kleisli.Hom.of (mediator_step R ξ σ X))
  · apply GuardedElgotMonadHom.ext
    apply MonadHom.ext
    funext X
    change (baseEmbedding T H R).hom.app X ≫ m.hom.app X = ξ.hom.app X
    rw [baseEmbedding_app, mediatorHom_app]
    exact (pure_comp_of S.monad _ _).symm.trans (congrArg Kleisli.Hom.of (mediator_base R ξ σ X))
  · rintro n ⟨hs, hb⟩
    have hs' := (guardedBimodule_post (resumptionGenerator R) n).symm.trans (congrArg Subtype.val hs)
    have step (X : C) : liftStep T H R X ≫ n.hom.app X = σ.val.app X := by
      have e := congrArg (fun τ => (τ : H ⟶ (S.monad : C ⥤ C)).app X) hs'
      change (suspension T H R).app X ≫ n.hom.app X = σ.val.app X at e
      simpa only [suspension_app] using e
    have base (X : C) : liftBase T H R X ≫ n.hom.app X = ξ.hom.app X := by
      have e := congrArg (fun h : T ⟶ S => h.hom.app X) hb
      change (baseEmbedding T H R).hom.app X ≫ n.hom.app X = ξ.hom.app X at e
      simpa only [baseEmbedding_app] using e
    apply GuardedElgotMonadHom.ext
    apply MonadHom.ext
    funext X
    rw [mediatorHom_app]
    exact mediator_unique R ξ σ n base step X

end Silmaril.Calco2019.Proofs
