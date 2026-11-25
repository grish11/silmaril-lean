module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Product.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedProductFan

/-! # Binary product laws in the common extended value category -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits
open Extension.Singleton (ofType productFst productSnd discardArrow pairArrows ProjectedCopyingReturn)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  (includeProjection : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Step Γ r s L → Seed Γ r s L)

set_option hygiene false in
local notation "obj" => ofType (Φ := Φ) Seed

/-- The canonical sequential pairing is the unique possible lift. Its membership and
both projection β equations therefore suffice for a product. -/
theorem productFan_isLimit_iff (A B : τ) :
    Nonempty (IsLimit (productFan pe Seed includeProjection A B)) ↔
      ∀ {X : τ} {f : obj X ⟶ obj A} {g : obj X ⟶ obj B},
        ProjectedCopyingReturn Seed pe f → ProjectedCopyingReturn Seed pe g →
        let p := pairArrows Seed f g
        ProjectedCopyingReturn Seed pe p ∧ p ≫ productFst Seed A B = f ∧ p ≫ productSnd Seed A B = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedProductFan.productFan_isLimit_iff pe Seed includeProjection A B

/-- With guarded unit η, all the chosen binary fans are products exactly when pairing has
a default central copying lift and projected copying returns preserve discard. -/
theorem all_productFans_isLimit_iff
    (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, WithUnitEta.Step Γ r s L → Seed Γ r s L) :
    (∀ A B : τ, Nonempty (IsLimit (productFan pe Seed includeProjection A B))) ↔
      (∀ {X A B : τ} {f : obj X ⟶ obj A} {g : obj X ⟶ obj B},
        ProjectedCopyingReturn Seed pe f → ProjectedCopyingReturn Seed pe g →
        ∃ p : Paper.TypeCategory.ofType (Φ := Φ) X ⟶ Paper.TypeCategory.ofType (product A B),
          Paper.TypeCategory.CentralCopies p ∧
            (Paper.Extension.Singleton.projection Seed).map p = pairArrows Seed f g) ∧
      (∀ {X A : τ} {f : obj X ⟶ obj A},
        ProjectedCopyingReturn Seed pe f → f ≫ discardArrow Seed A = discardArrow Seed X) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedProductFan.all_productFans_isLimit_iff pe Seed includeProjection includeUnit

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns
