module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Outward.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CaseCfg

/-! # A typed case as a two-block CFG -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]

/-- A case denotes the same arrow as a CFG that sends the selected payload to
one of two local blocks. The case scrutinee may have effects. -/
theorem denoteRegion_caseCfg
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {Γ : VCtx τ} {L : LCtx τ} {e : Tm Φ} {A B : τ} {l r : Region Φ}
    (he : Tm.HasType Γ e (Silmaril.coprod A B))
    (hl : Region.HasType (A :: Γ) l L) (hr : Region.HasType (B :: Γ) r L) :
    ∃ ht : Region.HasType Γ
      (.cfg (.case e (.br 0 (.var 0)) (.br 1 (.var 0))) 2
        (fun i => Region.renameLabels (fun j => 2 + j) (Fin.cases l (fun _ => r) i))) L,
      denoteRegion J M (.case he hl hr) = denoteRegion J M ht := by
  obtain ⟨ht, _, d, dt⟩ := Proofs.SSA.Isotope.LambdaSSA.Rewrite.caseCfg_common J M hu he hl hr
  exact ⟨ht, (RegionDenotes.eq_denote J M d).symm.trans (RegionDenotes.eq_denote J M dt)⟩

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
