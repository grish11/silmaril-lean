module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Singleton

/-! # A selected term denotation under singleton value substitution -/

public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- Supply the only free slot by a selected value arrow. The tail of the
substitution is immaterial because the original context is a singleton. -/
theorem Denotes.substSingleton {Δ : VCtx τ} {X D : τ} {t : Tm Φ} {ht : Tm.HasType [X] t D}
    {f : J.obj (ctxObj M [X]) ⟶ J.obj (M.obj D)} (d : Denotes J M ht f)
    (σ : Nat → Tm Φ) {hv : Tm.HasType Δ (σ 0) X} {v : ctxObj M Δ ⟶ M.obj X}
    (dv : Denotes J M hv (J.map v)) :
    ∃ h : Tm.HasType Δ (t.subst σ) D,
      Denotes J M h (J.map (v ≫ (λ_ (M.obj X)).inv) ≫ f) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Singleton.denotes_subst J M d σ dv

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
