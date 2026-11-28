module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Comparison.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Comparison.Replay

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open Region.Paper.RetainedLet (returnOnce)

universe u v w

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] {pe : ε}
  {Γ : VCtx (Ty α)} {A B D : Ty α} {a b : Tm Φ}

local notation "Typed" => Tm.HasType
local notation "ReturnEq" => fun (Γ : VCtx (Ty α)) (a b : Tm Φ) (A : Ty α) =>
  ReplayEqv pe Γ (returnOnce a) (returnOnce b) [A]

set_option backward.isDefEq.respectTransparency false

theorem unit_case_beta_proof (h : Typed Γ (.var 0 : Tm Φ) (Ty.coprod Ty.unit Ty.unit))
    (k : Typed (Ty.coprod Ty.unit Ty.unit :: Γ) b B) :
    ReturnEq Γ (.let₁ (.case (.var 0) (.inl .unit) (.inr .unit)) b)
      (b.subst (Tm.singleSubst (.case (.var 0) (.inl .unit) (.inr .unit)))) B := by
  have slot : Tm.BranchValue (Ty.unit :: Γ) (.var 0 : Tm Φ) Ty.unit := .var rfl
  have unit := (unit_eta (pe := pe) slot.hasType).symm.trans (let_beta_branch slot .unit)
  have changeArms := case_congr (pe := pe) h h (.inl .unit) (.inl slot.hasType)
    (.inr .unit) (.inr slot.hasType) (return_refl h)
    (inl_congr .unit slot.hasType unit.symm) (inr_congr .unit slot.hasType unit.symm)
  exact let_beta_of_value (.case h (.inl .unit) (.inr .unit)) k (.var (by cases h; assumption))
    (changeArms.trans (case_eta h))

omit [HasTy Φ (Ty α)] [HasEff Φ ε] in
theorem subst_lift_single (k : Tm Φ) (σ : Nat → Tm Φ) (v : Tm Φ) :
    (k.subst (Tm.liftSubst σ)).subst (Tm.singleSubst v) = k.subst (Tm.consSubst v σ) := by
  rw [Tm.subst_comp]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    change ((σ i).rename Nat.succ).subst (Tm.singleSubst v) = σ i
    rw [Tm.subst_rename]
    exact Tm.subst_var _

omit [HasTy Φ (Ty α)] [HasEff Φ ε] in
private theorem subst_lift_pair (k : Tm Φ) (σ : Nat → Tm Φ) (v w : Tm Φ) :
    (k.subst (Tm.liftSubst (Tm.liftSubst σ))).subst (Tm.consSubst w (Tm.singleSubst v)) =
      k.subst (Tm.consSubst w (Tm.consSubst v σ)) := by
  rw [Tm.subst_comp]
  congr 1
  funext i
  match i with
  | 0 | 1 => rfl
  | i + 2 =>
    change (((σ i).rename Nat.succ).rename Nat.succ).subst (Tm.consSubst w (Tm.singleSubst v)) = σ i
    rw [Tm.rename_comp, Tm.subst_rename]
    exact Tm.subst_var _

/-- A substitution by closed constructor values, with the original slot types. -/
def ConstructorSubst (Γ : VCtx (Ty α)) (σ : Nat → Tm Φ) : Prop :=
  ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue [] (σ i) A

omit [HasTy Φ (Ty α)] in
theorem ConstructorSubst.cons {σ : Nat → Tm Φ} {v : Tm Φ}
    (env : ConstructorSubst Γ σ) (value : Tm.BranchValue [] v A) :
    ConstructorSubst (A :: Γ) (Tm.consSubst v σ) := by
  intro i X hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact value
  | succ i => exact env hi

omit [HasTy Φ (Ty α)] in
theorem ConstructorSubst.nil (σ : Nat → Tm Φ) : ConstructorSubst ([] : VCtx (Ty α)) σ := by
  intro _ _ atSlot
  cases atSlot

theorem ConstructorSubst.typed {σ : Nat → Tm Φ} (env : ConstructorSubst Γ σ) :
    Tm.Subst.HasType Γ [] σ := by
  intro i X hi
  exact (env hi).hasType

/-- Purity excludes instruction calls by the signature hypothesis. Under a
constructor assignment, structural recursion evaluates only the taken case arm. -/
theorem normalize_pure (noPure : ∀ f : Φ, ¬ IsPure pe f)
    (h : Typed Γ a A) (pure : Tm.Pure pe a)
    {σ : Nat → Tm Φ} (values : ConstructorSubst Γ σ) :
    ∃ v, Tm.BranchValue [] v A ∧ ReturnEq [] (a.subst σ) v A := by
  induction h generalizing σ with
  | var hi => exact ⟨_, values hi, return_refl (values hi).hasType⟩
  | unit => exact ⟨.unit, .unit, return_refl .unit⟩
  | op _ _ =>
    cases pure with
    | op hf _ => exact False.elim (noPure _ hf)
  | pair ha hb ia ib =>
    cases pure with
    | pair pa pb =>
      obtain ⟨x, hx, ex⟩ := ia pa values
      obtain ⟨y, hy, ey⟩ := ib pb values
      exact ⟨.pair x y, .pair hx hy,
        pair_congr (ha.subst values.typed) hx.hasType (hb.subst values.typed) hy.hasType ex ey⟩
  | inl ha ih =>
    cases pure with
    | inl pa =>
      obtain ⟨x, hx, ex⟩ := ih pa values
      exact ⟨.inl x, .inl hx, inl_congr (ha.subst values.typed) hx.hasType ex⟩
  | inr ha ih =>
    cases pure with
    | inr pa =>
      obtain ⟨x, hx, ex⟩ := ih pa values
      exact ⟨.inr x, .inr hx, inr_congr (ha.subst values.typed) hx.hasType ex⟩
  | let₁ ha hb ia ib =>
    cases pure with
    | let₁ pa pb =>
      obtain ⟨x, hx, ex⟩ := ia pa values
      obtain ⟨y, hy, ey⟩ := ib pb (values.cons hx)
      let body := hb.subst (values.typed.lift _)
      have beta := let_beta_branch (pe := pe) hx body
      rw [subst_lift_single] at beta
      exact ⟨y, hy, (let_congr (ha.subst values.typed) hx.hasType body body ex (return_refl body)).trans
        (beta.trans ey)⟩
  | let₂ ha hb ia ib =>
    cases pure with
    | let₂ pa pb =>
      obtain ⟨x, hx, ex⟩ := ia pa values
      cases hx with
      | var bad => cases bad
      | pair hv hw =>
        obtain ⟨y, hy, ey⟩ := ib pb ((values.cons hv).cons hw)
        let body := hb.subst ((values.typed.lift _).lift _)
        have beta := let₂_beta_branch (pe := pe) hv hw body
        rw [subst_lift_pair] at beta
        exact ⟨y, hy, (let₂_congr (ha.subst values.typed) (.pair hv.hasType hw.hasType)
          body body ex (return_refl body)).trans (beta.trans ey)⟩
  | case he hl hr ie il ir =>
    cases pure with
    | case pe' pl pr =>
      obtain ⟨x, hx, ex⟩ := ie pe' values
      let left := hl.subst (values.typed.lift _)
      let right := hr.subst (values.typed.lift _)
      have scr := case_congr (pe := pe) (he.subst values.typed)
        hx.hasType left left right right ex (return_refl left) (return_refl right)
      cases hx with
      | var bad => cases bad
      | inl hv =>
        obtain ⟨y, hy, ey⟩ := il pl (values.cons hv)
        have beta := (case_beta_left (pe := pe) hv.hasType left right).trans (let_beta_branch hv left)
        rw [subst_lift_single] at beta
        exact ⟨y, hy, scr.trans (beta.trans ey)⟩
      | inr hv =>
        obtain ⟨y, hy, ey⟩ := ir pr (values.cons hv)
        have beta := (case_beta_right (pe := pe) hv.hasType left right).trans (let_beta_branch hv right)
        rw [subst_lift_single] at beta
        exact ⟨y, hy, scr.trans (beta.trans ey)⟩
  | abort _ ih =>
    cases pure with
    | abort pa =>
      obtain ⟨_, h, _⟩ := ih pa values
      cases h with
      | var bad => cases bad

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
