module

public import Silmaril.Semantics.Calco2019.InductiveResumption.Free.Defs
import Silmaril.Proofs.Semantics.Calco2019.InductiveResumptionFree

/-! # The ordinary free-extension property of inductive resumptions -/

public section

universe u v

namespace Silmaril.Calco2019.Inductive

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (P : Coproducts C)
  {T S : CategoryTheory.Monad C} {H : C ⥤ C}
  (R : InitialResumptions (Exception.parametrized P T H))

/-- The base monad embeds into inductive resumptions. -/
noncomputable def baseEmbedding : T ⟶ R.monad :=
  Proofs.InductiveResumptionFree.baseEmbedding P R

@[simp]
theorem baseEmbedding_app (X : C) : (baseEmbedding P R).app X = liftBase P R X :=
  Proofs.InductiveResumptionFree.baseEmbedding_app P R X

/-- The suspended operation generator. -/
noncomputable def suspension : H ⟶ (R.monad : C ⥤ C) :=
  Proofs.InductiveResumptionFree.suspension P R

@[simp]
theorem suspension_app (X : C) : (suspension P R).app X = liftStep P R X :=
  Proofs.InductiveResumptionFree.suspension_app P R X

variable (ξ : T ⟶ S) (σ : H ⟶ (S : C ⥤ C))

/-- The fold into the interpreting algebra is a monad morphism. -/
noncomputable def interpretationHom : R.monad ⟶ S :=
  Proofs.InductiveResumptionFree.interpretationHom P ξ σ R

@[simp]
theorem interpretationHom_app (X : C) :
    (interpretationHom P R ξ σ).app X = interpretation P ξ σ R X :=
  Proofs.InductiveResumptionFree.interpretationHom_app P ξ σ R X

/-- The algebra structure equation for the explicit mediator. -/
theorem interpretation_roll (X : C) :
    R.roll X ≫ interpretation P ξ σ R X =
      ((Exception.parametrized P T H).parameter X).map (interpretation P ξ σ R X) ≫
        interpretationAlgebra P ξ σ X :=
  Proofs.InductiveResumptionFree.interpretation_roll P ξ σ R X

/-- With the chosen initial algebras, the inductive resumption monad freely extends the base. -/
theorem resumption_free :
    (monadBimodule C).IsFreeExtension (suspension P R) (baseEmbedding P R) :=
  Proofs.InductiveResumptionFree.resumption_free P R

/-- The identity monad is initial in the ordinary monad category. -/
noncomputable def identity_initial : IsInitial (CategoryTheory.Monad.id C) :=
  Proofs.InductiveResumptionFree.identity_initial

/-- The identity-base inductive resumption is the free monad on the endofunctor. -/
theorem resumption_freeOn
    (R₀ : InitialResumptions (Exception.parametrized P (CategoryTheory.Monad.id C) H)) :
    (monadBimodule C).IsFreeObject (suspension P R₀) :=
  Proofs.InductiveResumptionFree.resumption_freeOn P R₀

end Silmaril.Calco2019.Inductive
