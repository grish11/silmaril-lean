module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Product.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Return.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedValueProduct

/-! # Pairing and projection laws for extended singleton quotients -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

set_option hygiene false in
local notation "obj" => ofType (Φ := Φ) Seed

/-- Projection β for the first component uses discard compatibility of the right leg. -/
theorem pairing_fst_of_discard {X A B : τ} (f : obj X ⟶ obj A) (g : obj X ⟶ obj B)
    (hg : g ≫ discardArrow Seed B = discardArrow Seed X) :
    pairArrows Seed f g ≫ productFst Seed A B = f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedValueProduct.pairing_fst_of_discard Seed f g hg

/-- Projection β for the second component uses discard compatibility of the left leg. -/
theorem pairing_snd_of_discard {X A B : τ} (f : obj X ⟶ obj A) (g : obj X ⟶ obj B)
    (hf : f ≫ discardArrow Seed A = discardArrow Seed X) :
    pairArrows Seed f g ≫ productSnd Seed A B = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedValueProduct.pairing_snd_of_discard Seed f g hf

/-- The guarded first projection preserves discard. -/
theorem fst_discard (A B : τ) :
    productFst Seed A B ≫ discardArrow Seed A = discardArrow Seed (product A B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedValueProduct.fst_discard Seed A B

/-- The guarded second projection preserves discard. -/
theorem snd_discard (A B : τ) :
    productSnd Seed A B ≫ discardArrow Seed B = discardArrow Seed (product A B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedValueProduct.snd_discard Seed A B

/-- An arrow with a default central copying lift is recovered by pairing its projections. -/
theorem pairing_reconstruct {X A B : τ} {p : obj X ⟶ obj (product A B)}
    (hp : ∃ p₀ : Paper.TypeCategory.ofType (Φ := Φ) X ⟶ Paper.TypeCategory.ofType (product A B),
      Paper.TypeCategory.CentralCopies p₀ ∧ (projection Seed).map p₀ = p) :
    pairArrows Seed (p ≫ productFst Seed A B) (p ≫ productSnd Seed A B) = p :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedValueProduct.pairing_reconstruct Seed hp

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option backward.isDefEq.respectTransparency false in
/-- The two typed pure-return lifts provide a typed pure-return lift of the pairing. -/
theorem projectedPureReturn_pairArrows {X A B : τ} {f : obj X ⟶ obj A} {g : obj X ⟶ obj B}
    (hf : ProjectedPureReturn Seed pe f) (hg : ProjectedPureReturn Seed pe g) :
    ProjectedPureReturn Seed pe (pairArrows Seed f g) := by
  obtain ⟨f₀, hf₀, rfl⟩ := hf
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  exact ⟨_, Paper.TypeCategory.pureReturn_pairArrows hf₀ hg₀, map_pairArrows Seed f₀ g₀⟩

/-- An immediate constructor return belongs to the projected copying value category. -/
theorem projected_branchValue_mem {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    ProjectedCopyingReturn Seed pe (ofRegion Seed (.br (ℓ := 0) rfl ha)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedValueProduct.projected_branchValue_mem Seed pe ha

/-- The projections jointly determine arrows of the projected copying value category. -/
theorem projections_ext {X A B : τ} {p q : obj X ⟶ obj (product A B)}
    (hp : ProjectedCopyingReturn Seed pe p) (hq : ProjectedCopyingReturn Seed pe q)
    (hl : p ≫ productFst Seed A B = q ≫ productFst Seed A B) (hr : p ≫ productSnd Seed A B = q ≫ productSnd Seed A B) :
    p = q :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedValueProduct.projections_ext Seed pe hp hq hl hr

/-- A cone with two constructor-return legs has a unique lift among projected copying values. -/
theorem constructor_pair_existsUnique {X A B : τ} {a b : Tm Φ}
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    ∃! p : obj X ⟶ obj (product A B),
      ProjectedCopyingReturn Seed pe p ∧
        p ≫ productFst Seed A B = ofRegion Seed (.br (ℓ := 0) rfl ha) ∧
        p ≫ productSnd Seed A B = ofRegion Seed (.br (ℓ := 0) rfl hb) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedValueProduct.constructor_pair_existsUnique Seed pe ha hb

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
