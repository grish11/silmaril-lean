module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Free.Defs
public import Silmaril.Semantics.Calco2019.ExceptionResumption.Interpretation.Iteration
public import Silmaril.Semantics.Calco2019.ExceptionResumption.Interpretation.Uniqueness
import Silmaril.Proofs.Semantics.Calco2019.ExceptionResumptionFree

/-! # Free extensions by an endofunctor, CALCO 2019 Theorem 28 -/

public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasInitial C] {P : Coproducts C}
  {T : GuardedElgotMonad P} {H : C ⥤ C}
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)

/-- The resumption monad is free under the specified base and suspension embeddings. -/
theorem resumption_free :
    (guardedBimodule P).IsFreeExtension (resumptionGenerator R) (baseEmbedding T H R) :=
  Proofs.resumption_free R

/-- Theorem 28, packaged as the free extension of Definition 2. -/
@[expose]
noncomputable def freeExtension : (guardedBimodule P).FreeExtension H T where
  pt := (parametrizedElgot T H).resumptionElgotMonad R
  generator := resumptionGenerator R
  inclusion := baseEmbedding T H R
  isFreeExtension := resumption_free R

omit [HasInitial C] in
/-- For the guarded identity base, the coalgebra's endofunctor has object action
`Z ↦ X + H Z`. -/
theorem identityParameter_obj (H : C ⥤ C) (X Z : C) :
    ((parametrizedElgot (guardedIdentity P) H).toParametrizedMonad.parameter X).obj Z =
      P.sum X (H.obj Z) :=
  rfl

omit [HasInitial C] in
/-- Its action on maps fixes the return summand and applies `H` on the right. -/
theorem identityParameter_map (H : C ⥤ C) (X : C) {Z Z' : C} (f : Z ⟶ Z') :
    ((parametrizedElgot (guardedIdentity P) H).toParametrizedMonad.parameter X).map f =
      P.map (𝟙 X) (H.map f) :=
  rfl

/-- Corollary 29. The identity-based final-coalgebra resumptions and the base
monad have the exception resumptions as their coproduct of guarded Elgot monads. -/
theorem resumption_coproduct
    (R₀ : FinalResumptions (parametrizedElgot (guardedIdentity P) H).toParametrizedMonad) :
    ∃! l : (parametrizedElgot (guardedIdentity P) H).resumptionElgotMonad R₀ ⟶
        (parametrizedElgot T H).resumptionElgotMonad R,
      (guardedBimodule P).post (resumptionGenerator R₀) l = resumptionGenerator R ∧
        Nonempty (IsColimit (BinaryCofan.mk l (baseEmbedding T H R))) :=
  coproduct_of_free_extensions (freeExtension R₀) (freeExtension R)

end Silmaril.Calco2019.Exception
