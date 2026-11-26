module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Observation
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Substitution

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Resumption
open Silmaril.Isotope.LambdaSSA.Resumption.Typing

universe u v w x

variable {Φ : Type u} {α : Type w} {σ : Type x} {O : Ops Φ α σ} {env : Env α}
  {a : LambdaSSA.Tm Φ} {l r : LambdaSSA.Region Φ} {v : Value α}

private theorem let_pure (h : PureValue O env a v) :
    RegionAt O env (.let₁ a r) (extend env v) r where
  eval := by
    intro s j out t
    constructor
    · intro run; cases run with
      | let₁ head body => obtain ⟨rfl, rfl⟩ := h.unique head; exact body
    · exact fun run => .let₁ (h.eval _) run
  fault := by
    intro s t
    constructor
    · intro run; cases run with
      | let₁_arg head => exact (h.noFault head).elim
      | let₁_body head body => obtain ⟨rfl, rfl⟩ := h.unique head; exact body
    · exact fun run => .let₁_body (h.eval _) run
  div := by
    intro s
    constructor
    · intro run; cases run.unfold with
      | let₁_arg head => exact (h.noDiv head).elim
      | core step => cases step with
        | let₁ head body => obtain ⟨rfl, rfl⟩ := h.unique head; exact body
    · exact fun run => .fold_core (.let₁ (h.eval _) run)

theorem letValue {τ : Type v} [TypeFormers τ] {Γ : VCtx τ} {A : τ}
    (ha : a.BranchValue Γ A) : RegionAt O env (.let₁ a r) env (r.substVars (LambdaSSA.Tm.singleSubst a)) := by
  obtain ⟨v, value⟩ := PureValue.ofBranchValue (O := O) (env := env) ha
  exact (let_pure value).trans ((Realizes.single value).region r).symm

theorem caseInl : RegionAt O env (.case (.inl a) l r) env (.let₁ a l) where
  eval := by
    intro s i out t
    constructor
    · intro run; cases run with
      | case_inl head body => cases head with | inl head => exact .let₁ head body
      | case_inr head _ => cases head
    · intro run; cases run with | let₁ head body => exact .case_inl (.inl head) body
  fault := by
    intro s t
    constructor
    · intro run; cases run with
      | case_arg head => cases head with | inl head => exact .let₁_arg head
      | case_inl head body => cases head with | inl head => exact .let₁_body head body
      | case_inr head _ => cases head
    · intro run; cases run with
      | let₁_arg head => exact .case_arg (.inl head)
      | let₁_body head body => exact .case_inl (.inl head) body
  div := by
    intro s
    constructor
    · intro run; cases run.unfold with
      | case_arg head => cases head with | inl head => exact .fold (.let₁_arg head)
      | core step => cases step with
        | case_inl head body => cases head with | inl head => exact .fold_core (.let₁ head body)
        | case_inr head _ => cases head
    · intro run; cases run.unfold with
      | let₁_arg head => exact .fold (.case_arg (.inl head))
      | core step => cases step with
        | let₁ head body => exact .fold_core (.case_inl (.inl head) body)

theorem caseInr : RegionAt O env (.case (.inr a) l r) env (.let₁ a r) where
  eval := by
    intro s i out t
    constructor
    · intro run; cases run with
      | case_inl head _ => cases head
      | case_inr head body => cases head with | inr head => exact .let₁ head body
    · intro run; cases run with | let₁ head body => exact .case_inr (.inr head) body
  fault := by
    intro s t
    constructor
    · intro run; cases run with
      | case_arg head => cases head with | inr head => exact .let₁_arg head
      | case_inl head _ => cases head
      | case_inr head body => cases head with | inr head => exact .let₁_body head body
    · intro run; cases run with
      | let₁_arg head => exact .case_arg (.inr head)
      | let₁_body head body => exact .case_inr (.inr head) body
  div := by
    intro s
    constructor
    · intro run; cases run.unfold with
      | case_arg head => cases head with | inr head => exact .fold (.let₁_arg head)
      | core step => cases step with
        | case_inl head _ => cases head
        | case_inr head body => cases head with | inr head => exact .fold_core (.let₁ head body)
    · intro run; cases run.unfold with
      | let₁_arg head => exact .fold (.case_arg (.inr head))
      | core step => cases step with
        | let₁ head body => exact .fold_core (.case_inr (.inr head) body)

variable {κ : Type v} [HasTy Φ (Ty κ)] {Γ : VCtx (Ty κ)}

omit [HasTy Φ (Ty κ)] in
theorem branchValue_pure_typed {A : Ty κ} (ha : a.BranchValue Γ A)
    {atomType : α → κ → Prop} (typed : EnvTyped atomType Γ env) :
    ∃ v, PureValue O env a v ∧ ValueTyped atomType v A := by
  induction ha with
  | var h => exact ⟨_, .var _, typed h⟩
  | unit => exact ⟨_, .unit, .unit⟩
  | pair _ _ left right =>
    obtain ⟨_, ha, hA⟩ := left
    obtain ⟨_, hb, hB⟩ := right
    exact ⟨_, ha.pair hb, .pair hA hB⟩
  | inl _ ih => obtain ⟨_, ha, hA⟩ := ih; exact ⟨_, ha.inl, .inl hA⟩
  | inr _ ih => obtain ⟨_, ha, hA⟩ := ih; exact ⟨_, ha.inr, .inr hA⟩

theorem caseValue {A B : Ty κ} (ha : a.BranchValue Γ (.coprod A B)) :
    ShapedObs (α := α) (σ := σ) Γ
      (.case a (r.substVars (LambdaSSA.Tm.replaceNewest (.inl (.var 0))))
        (r.substVars (LambdaSSA.Tm.replaceNewest (.inr (.var 0)))))
      (r.substVars (LambdaSSA.Tm.singleSubst a)) := by
  intro O atomType _ env typed
  obtain ⟨v, value, shape⟩ := branchValue_pure_typed (O := O) ha typed
  cases shape with
  | inl =>
    exact (case_pure_inl value).trans (((Realizes.replace _ _).1.region r).trans
      ((Realizes.single value).region r).symm)
  | inr =>
    exact (case_pure_inr value).trans (((Realizes.replace _ _).2.region r).trans
      ((Realizes.single value).region r).symm)

theorem initial {t : LambdaSSA.Region Φ} (ha : a.BranchValue Γ (.empty : Ty κ)) :
    ShapedObs (α := α) (σ := σ) Γ r t := by
  intro O atomType _ env typed
  obtain ⟨_, _, shape⟩ := branchValue_pure_typed (O := O) ha typed
  cases shape

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation
