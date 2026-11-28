module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Syntax.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms


/-! # Native normalization of cases after binding the discriminator -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithCaseBindNormalization

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open Paper.Extension (Eqv ReturnDiscards)
open Paper.RetainedCase (boundCase)
open CfgEta.TypeCategory (returnRegion returnRegion_typed)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

private theorem literalUnit_bind
    (unitEta : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → S Γ r s L)
    {Γ : VCtx τ} {L : LCtx τ} {u : Tm Φ} {p : Region Φ}
    (hu : Tm.BranchValue Γ u unit) (hp : ValueBranches (unit :: Γ) p L) :
    Eqv S Γ (.let₁ .unit p) (p.substVars (Tm.singleSubst u)) L := by
  have e : Eqv S [unit] (.br 0 .unit) (.br 0 (.var 0)) [unit] :=
    .extra (.br rfl .unit) (.br rfl (.var (i := 0) rfl)) (unitEta .unit)
  have value : Eqv S Γ (.br 0 .unit) (.br 0 u) [unit] := by
    apply e.substVars (θ := Tm.singleSubst u)
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact hu
    | succ i => simp [At] at hi
  have post : LSubst.HasType Γ [unit] L (fun _ => p) := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact hp.hasType
    | succ i => simp [At] at hi
  have beta := Paper.Extension.Eqv.paper (Seed := S)
    (.cfgEta (.native (.letValue Tm.BranchValue.unit hp.hasType)))
  exact beta.trans (value.lsubstPost (.br rfl .unit) (.br rfl hu) post)

theorem case_return_bit
    (bind : ∀ {Γ L r s}, Paper.WithCaseBind.Step Γ r s L → S Γ r s L)
    (unary : ∀ {Γ L r s}, Paper.UnaryReturn.Step Γ r s L → S Γ r s L)
    (unitEta : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → S Γ r s L)
    {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {slot : Nat}
    (ha : Tm.HasType Γ a (coprod unit unit)) (out : At L slot (coprod unit unit)) :
    Eqv S Γ
      (.case a (.let₁ .unit (.br slot (.inl (.var 0)))) (.let₁ .unit (.br slot (.inr (.var 0)))))
      ((returnRegion a).renameLabels (fun _ => slot)) L := by
  let left : Region Φ := .let₁ .unit (.br slot (.inl (.var 0)))
  let right : Region Φ := .let₁ .unit (.br slot (.inr (.var 0)))
  let Bit := (coprod unit unit : τ)
  have hl : ValueBranches (unit :: Γ) left L :=
    .let₁ .unit (.br out (.inl (.var (i := 0) rfl)))
  have hr : ValueBranches (unit :: Γ) right L :=
    .let₁ .unit (.br out (.inr (.var (i := 0) rfl)))
  have elimLeft : Eqv S (unit :: Bit :: Γ) left (.br slot (.inl (.var 0))) L :=
    literalUnit_bind unitEta (.var (i := 0) rfl) (.br out (.inl (.var (i := 0) rfl)))
  have elimRight : Eqv S (unit :: Bit :: Γ) right (.br slot (.inr (.var 0))) L :=
    literalUnit_bind unitEta (.var (i := 0) rfl) (.br out (.inr (.var (i := 0) rfl)))
  have retag : Eqv S (Bit :: Γ) (boundCase left right) (.br slot (.var 0)) L :=
    (Eqv.case (.var (i := 0) rfl) elimLeft elimRight).trans
      (.paper (.cfgEta (.native (.caseValue (.var (i := 0) rfl) (.br out (.var (i := 0) rfl))))))
  refine (Paper.WithCaseBind.case_eq_return_post bind unary ha hl hr).trans ?_
  rw [renameLabels_eq_lsubst]
  apply Eqv.lsubstCongr (returnRegion_typed ha)
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact retag
  | succ i => simp [At] at hi


private theorem instantiate_weaken (p : Region Φ) (a : Tm Φ) :
    (p.renameVars Nat.succ).substVars (Tm.singleSubst a) = p := by
  rw [substVars_renameVars]
  exact substVars_var p

private theorem ignore_value_case {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ} {p : Region Φ}
    (ha : Tm.BranchValue Γ a (coprod A B)) (hp : HasType Γ p L) :
    Eqv S Γ (.case a (p.renameVars Nat.succ) (p.renameVars Nat.succ)) p L := by
  have keep (v : Tm Φ) :
      (p.renameVars Nat.succ).substVars (Tm.replaceNewest v) = p.renameVars Nat.succ := by
    rw [substVars_renameVars, renameVars_eq_substVars]
    rfl
  have h := Eqv.paper (Seed := S) (.cfgEta (.native
    (.caseValue ha (hp.renameVars (Ren.wk Γ (coprod A B))))))
  simpa only [keep, instantiate_weaken] using h

theorem case_eq_of_returnDiscards
    (bind : ∀ {Γ L r s}, Paper.WithCaseBind.Step Γ r s L → S Γ r s L)
    (unary : ∀ {Γ L r s}, Paper.UnaryReturn.Step Γ r s L → S Γ r s L)
    {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ} {p : Region Φ}
    (ha : Tm.HasType Γ a (coprod A B)) (hp : ValueBranches Γ p L) (drop : ReturnDiscards S Γ a) :
    Eqv S Γ (.case a (p.renameVars Nat.succ) (p.renameVars Nat.succ)) p L := by
  let Sum := coprod A B
  let post : Nat → Region Φ := fun _ => p.renameVars Nat.succ
  have moved := Paper.WithCaseBind.case_eq_return_post bind unary ha
    (hp.renameVars (Ren.wk Γ A)) (hp.renameVars (Ren.wk Γ B))
  have ignoreBound : Eqv S (Sum :: Γ) (boundCase (post 0) (post 0)) (post 0) L := by
    have ignore := ignore_value_case (S := S)
      (.var (i := 0) (rfl : At (Sum :: Γ) 0 Sum)) (hp.hasType.renameVars (Ren.wk Γ Sum))
    have h : lift Nat.succ ∘ Nat.succ = Nat.succ ∘ Nat.succ := rfl
    simpa only [boundCase, post, renameVars_comp, h] using ignore
  have changed : Eqv S Γ
      ((returnRegion a).lsubst (fun _ => boundCase (post 0) (post 0))) ((returnRegion a).lsubst post) L := by
    apply Eqv.lsubstCongr (returnRegion_typed ha)
    intro i T hi
    cases i with
    | zero => cases Option.some.inj hi; exact ignoreBound
    | succ i => simp [At] at hi
  have discardPost : LSubst.HasType Γ [unit] L post := by
    intro i T hi
    cases i with
    | zero => cases Option.some.inj hi; exact hp.hasType.renameVars (Ren.wk Γ unit)
    | succ i => simp [At] at hi
  have discarded := Eqv.lsubstPost drop
    ((returnRegion_typed ha).lsubst (fun _ _ _ => .br rfl .unit)) (.br rfl .unit) discardPost
  have compose : compLSubst (fun _ => .br 0 .unit) post = post := by
    funext i
    change ((p.renameVars Nat.succ).renameVars (lift Nat.succ)).substVars (Tm.singleSubst .unit) =
      p.renameVars Nat.succ
    rw [renameVars_comp, substVars_renameVars, renameVars_eq_substVars]
    rfl
  rw [lsubst_comp, compose] at discarded
  change Eqv S Γ ((returnRegion a).lsubst post)
    ((p.renameVars Nat.succ).substVars (Tm.singleSubst .unit)) L at discarded
  rw [instantiate_weaken] at discarded
  exact moved.trans (changed.trans discarded)


end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithCaseBindNormalization
