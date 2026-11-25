module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Product.Thms

/-! # Binary fan criteria in the guarded projection and unit extensions -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedProductFan

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open Paper.WithProjectionReturns (Step productFan)
open CfgEta.TypeCategory (productFstBranches productSndBranches)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  (includeProjection : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Step Γ r s L → Seed Γ r s L)
  (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)

set_option hygiene false in
local notation "Values" => ProjectedCopyingValueCategory Seed pe
set_option hygiene false in
local notation "obj" => ofType (Φ := Φ) Seed
local notation "U" => (Silmaril.unit : τ)

set_option backward.isDefEq.respectTransparency false in
theorem productFan_isLimit_iff (A B : τ) :
    Nonempty (IsLimit (productFan pe Seed includeProjection A B)) ↔
      ∀ {X : τ} {f : obj X ⟶ obj A} {g : obj X ⟶ obj B},
        ProjectedCopyingReturn Seed pe f → ProjectedCopyingReturn Seed pe g →
        let p := pairArrows Seed f g
        ProjectedCopyingReturn Seed pe p ∧ p ≫ productFst Seed A B = f ∧ p ≫ productSnd Seed A B = g := by
  constructor
  · rintro ⟨h⟩ X f g hf hg
    let cone : BinaryFan (⟨obj A⟩ : Values) (⟨obj B⟩ : Values) := BinaryFan.mk ⟨f, hf⟩ ⟨g, hg⟩
    let p := h.lift cone
    have hl : p.1 ≫ productFst Seed A B = f := congrArg (·.1) (h.fac cone ⟨WalkingPair.left⟩)
    have hr : p.1 ≫ productSnd Seed A B = g := congrArg (·.1) (h.fac cone ⟨WalkingPair.right⟩)
    have hp := pairing_reconstruct Seed p.2.2
    rw [hl, hr] at hp
    dsimp only
    rw [hp]
    exact ⟨p.2, hl, hr⟩
  · intro close
    let lift {X : Values} (f : X ⟶ ⟨obj A⟩) (g : X ⟶ ⟨obj B⟩) :
        X ⟶ (productFan pe Seed includeProjection A B).pt :=
      ⟨pairArrows Seed f.1 g.1, (close f.2 g.2).1⟩
    refine ⟨BinaryFan.IsLimit.mk _ (@lift) ?_ ?_ ?_⟩
    · intro X f g
      exact WideSubcategory.hom_ext _ (close f.2 g.2).2.1
    · intro X f g
      exact WideSubcategory.hom_ext _ (close f.2 g.2).2.2
    · intro X f g p hl hr
      apply WideSubcategory.hom_ext
      exact projections_ext Seed pe p.2 (lift f g).2
        ((congrArg (·.1) hl).trans (close f.2 g.2).2.1.symm)
        ((congrArg (·.1) hr).trans (close f.2 g.2).2.2.symm)

include includeUnit in
private theorem unit_return {Γ : VCtx τ} {i : Nat} (hi : At Γ i U) :
    Paper.Extension.Eqv Seed Γ (.br 0 (.unit : Tm Φ)) (.br 0 (.var i)) [U] := by
  have h : Paper.Extension.Eqv Seed [U] (.br 0 (.unit : Tm Φ)) (.br 0 (.var 0)) [U] :=
    .extra (.br rfl .unit) (.br rfl (.var rfl)) (includeUnit .unit)
  refine h.substVars (θ := fun _ => .var i) ?_
  intro j A hj
  cases j with
  | zero => cases Option.some.inj hj; exact .var hi
  | succ j => simp [At] at hj

include includeUnit in
private theorem unit_projections_eq : productFst Seed U U = productSnd Seed U U := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff Seed (productFstBranches U U) (productSndBranches U U)).2
  exact .let₂ (.var rfl) ((unit_return Seed includeUnit (i := 1) rfl).symm.trans
    (unit_return Seed includeUnit (i := 0) rfl))

set_option backward.isDefEq.respectTransparency false in
include includeUnit in
theorem all_productFans_isLimit_iff :
    (∀ A B : τ, Nonempty (IsLimit (productFan pe Seed includeProjection A B))) ↔
      (∀ {X A B : τ} {f : obj X ⟶ obj A} {g : obj X ⟶ obj B},
        ProjectedCopyingReturn Seed pe f → ProjectedCopyingReturn Seed pe g →
        ∃ p : Paper.TypeCategory.ofType (Φ := Φ) X ⟶ Paper.TypeCategory.ofType (product A B),
          Paper.TypeCategory.CentralCopies p ∧
            (Paper.Extension.Singleton.projection Seed).map p = pairArrows Seed f g) ∧
      (∀ {X A : τ} {f : obj X ⟶ obj A},
        ProjectedCopyingReturn Seed pe f → f ≫ discardArrow Seed A = discardArrow Seed X) := by
  constructor
  · intro products
    constructor
    · intro X A B f g hf hg
      exact ((productFan_isLimit_iff pe Seed includeProjection A B).mp (products A B) hf hg).1.2
    · intro X A f hf
      have ht : ProjectedCopyingReturn Seed pe (discardArrow Seed A) :=
        projected_branchValue_mem Seed pe (Tm.BranchValue.unit (Γ := [A]))
      have hx : ProjectedCopyingReturn Seed pe (discardArrow Seed X) :=
        projected_branchValue_mem Seed pe (Tm.BranchValue.unit (Γ := [X]))
      have hc := (ProjectedCopyingReturn Seed pe).comp_mem _ _ hf ht
      obtain ⟨_, hl, hr⟩ := (productFan_isLimit_iff pe Seed includeProjection U U).mp (products U U) hc hx
      exact hl.symm.trans ((congrArg (_ ≫ ·) (unit_projections_eq Seed includeUnit)).trans hr)
  · rintro ⟨close, discardCompat⟩ A B
    refine (productFan_isLimit_iff pe Seed includeProjection A B).mpr ?_
    intro X f g hf hg
    exact ⟨⟨projectedPureReturn_pairArrows Seed pe hf.1 hg.1, close hf hg⟩,
      pairing_fst_of_discard Seed f g (discardCompat hg),
      pairing_snd_of_discard Seed f g (discardCompat hf)⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedProductFan
