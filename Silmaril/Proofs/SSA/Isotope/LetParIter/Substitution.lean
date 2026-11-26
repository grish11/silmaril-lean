module

public import Silmaril.SSA.Isotope.LetParIter.Substitution.Defs
public import Silmaril.Proofs.SSA.Isotope.LetParIter.Interpretation

@[expose] public section

namespace Silmaril.Isotope.LetParIter.Proofs

open Parallel LetIter.ProofRelevant.Semantics

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]

/-- Build the native snoc environment from its dependent index view. -/
def envOf : {n : Nat} → (β : BoundCtx τ n) →
    ((i : Fin n) → TyDen (β.get i)) → BoundDen β
  | 0, .nil, _ => PUnit.unit
  | _ + 1, .snoc β _, f => (envOf β (fun i => f i.succ), f 0)

@[simp] theorem get_envOf {n : Nat} (β : BoundCtx τ n)
    (f : (i : Fin n) → TyDen (β.get i)) (i : Fin n) : BoundDen.get (envOf β f) i = f i := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β A ih => exact Fin.cases rfl (fun j => ih (fun k => f k.succ) j) i

@[simp] theorem envOf_get {n : Nat} {β : BoundCtx τ n} (ρ : BoundDen β) :
    envOf β (BoundDen.get ρ) = ρ := by
  induction β with
  | nil => cases ρ; rfl
  | snoc β A ih =>
      change (envOf β (BoundDen.get ρ.1), ρ.2) = ρ
      rw [ih]
      rfl

def pull {n k : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ k}
    (r : BoundCtx.Renaming β δ) (ρ : BoundDen δ) : BoundDen β :=
  envOf β fun i => r.typed i ▸ BoundDen.get ρ (r.toFun i)

@[simp] theorem pull_up {n k : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ k}
    (r : BoundCtx.Renaming β δ) (ρ : BoundDen δ) (A : τ) (a : TyDen A) :
    pull (r.up A) (ρ, a) = (pull r ρ, a) := by
  apply Prod.ext
  · apply congrArg (envOf β)
    funext i
    rfl
  · rfl

@[simp] theorem pull_succ {n : Nat} {β : BoundCtx τ n} (ρ : BoundDen β) (A : τ) (a : TyDen A) :
    pull (BoundCtx.Renaming.succ β A) (ρ, a) = ρ :=
  envOf_get ρ

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem pull_underBinder {n : Nat} {β : BoundCtx τ n} (ρ : BoundDen β)
    {X Y : τ} (x : TyDen X) (y : TyDen Y) :
    pull (BoundCtx.Renaming.underBinder β X Y) ((ρ, x), y) = (ρ, y) := by
  rw [BoundCtx.Renaming.underBinder, pull_up, pull_succ]

@[simp] theorem pull_underTwoBinders {n : Nat} {β : BoundCtx τ n} (ρ : BoundDen β)
    {X Y Z : τ} (x : TyDen X) (y : TyDen Y) (z : TyDen Z) :
    pull (BoundCtx.Renaming.underTwoBinders β X Y Z) (((ρ, x), y), z) = ((ρ, y), z) := by
  change ((envOf β (BoundDen.get ρ), y), z) = ((ρ, y), z)
  rw [envOf_get]

@[simp] theorem pull_leftResult {n : Nat} {β : BoundCtx τ n} (ρ : BoundDen β)
    {A B : τ} (a : TyDen A) (b : TyDen B) :
    pull (Typing.leftResultRenaming β A B) ((ρ, a), b) = (ρ, a) := by
  change (envOf β (BoundDen.get ρ), a) = (ρ, a)
  rw [envOf_get]

variable {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [Elgot.Iterate m] [InstructionModel Φ τ ε m]
variable (P : Elgot.ParallelPairing m)
variable {Γ : Ctx ν τ} {n k : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ k}
variable {a : Tm ν Φ n} {A : τ} (γ : CtxDen Γ)

private theorem denote_bv_cast (i : Fin k) (h : δ.get i = A) (ρ : BoundDen δ) :
    denote (ε := ε) P (h ▸ (Derivation.bv (Φ := Φ) (Γ := Γ) (β := δ) (i := i))) γ ρ =
      pure (h ▸ BoundDen.get ρ i) := by
  cases h
  rw [denote]

set_option backward.isDefEq.respectTransparency false in
theorem denote_rename (d : Derivation Φ Γ β a A) (r : BoundCtx.Renaming β δ) (ρ : BoundDen δ) :
    denote (ε := ε) P (Typing.rename r d) γ ρ = denote (ε := ε) P d γ (pull r ρ) := by
  induction d generalizing k δ with
  | fv | unit => simp only [Typing.rename, denote]
  | bv =>
      simp only [Typing.rename, denote, pull, get_envOf]
      exact denote_bv_cast P γ _ _ _
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
      simp only [Typing.rename, denote, ih]
  | let₁ _ _ iha ihb | let₂ _ _ iha ihb | iter _ _ iha ihb =>
      simp only [Typing.rename, denote, iha, ihb, pull_up]
  | pair _ _ iha ihb | par _ _ iha ihb =>
      simp only [Typing.rename, denote, iha, ihb]
  | case de dl dr ihe ihl ihr =>
      simp only [Typing.rename, denote, ihe, ihl, ihr, pull_up]

/-- Substitution images return the values prescribed by the old environment. -/
def SubstDen {σ : Fin n → Tm ν Φ k} (s : Subst (Γ := Γ) β δ σ)
    (ρ : BoundDen δ) (ξ : BoundDen β) : Prop :=
  ∀ i, denote (ε := ε) P (s i) γ ρ = pure (BoundDen.get ξ i)

set_option backward.isDefEq.respectTransparency false in
theorem SubstDen.up {σ : Fin n → Tm ν Φ k} {s : Subst (Γ := Γ) β δ σ}
    {ρ : BoundDen δ} {ξ : BoundDen β} (hs : SubstDen (ε := ε) P γ s ρ ξ)
    (B : τ) (b : TyDen B) :
    SubstDen (ε := ε) P γ (s.up B) (ρ, b) (ξ, b) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change denote (ε := ε) P (Derivation.bv (Φ := Φ) (Γ := Γ) (β := .snoc δ B)
      (i := 0)) γ (ρ, b) = pure b
    rw [denote]
    rfl
  · change denote (ε := ε) P (Typing.lift (B := B) (s j)) γ (ρ, b) =
      pure (BoundDen.get ξ j)
    rw [Typing.lift, denote_rename, pull_succ]
    exact hs j

set_option backward.isDefEq.respectTransparency false in
theorem denote_bsubst (d : Derivation Φ Γ β a A) {σ : Fin n → Tm ν Φ k}
    (s : Subst (Γ := Γ) β δ σ) (ρ : BoundDen δ) (ξ : BoundDen β)
    (hs : SubstDen (ε := ε) P γ s ρ ξ) :
    denote (ε := ε) P (Typing.bsubst s d) γ ρ = denote (ε := ε) P d γ ξ := by
  induction d generalizing k δ with
  | fv | unit => simp only [Typing.bsubst, denote]
  | bv => simpa only [Typing.bsubst, denote] using hs _
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
      simp only [Typing.bsubst, denote, ih s ρ ξ hs]
  | pair _ _ iha ihb | par _ _ iha ihb =>
      simp only [Typing.bsubst, denote, iha s ρ ξ hs, ihb s ρ ξ hs]
  | let₁ da db iha ihb =>
      rw [Typing.bsubst, denote, denote, iha s ρ ξ hs]
      apply bind_congr
      intro x
      exact ihb (s.up _) (ρ, x) (ξ, x) (SubstDen.up P γ hs _ x)
  | let₂ da db iha ihb =>
      rw [Typing.bsubst, denote, denote, iha s ρ ξ hs]
      apply bind_congr
      intro p
      exact ihb ((s.up _).up _) _ _ (SubstDen.up P γ (SubstDen.up P γ hs _ _) _ _)
  | case de dl dr ihe ihl ihr =>
      rw [Typing.bsubst, denote, denote, ihe s ρ ξ hs]
      apply bind_congr
      intro e
      cases TypeModel.coprodEquiv _ _ e with
      | inl x => exact ihl (s.up _) (ρ, x) (ξ, x) (SubstDen.up P γ hs _ x)
      | inr y => exact ihr (s.up _) (ρ, y) (ξ, y) (SubstDen.up P γ hs _ y)
  | iter da db iha ihb =>
      simp only [Typing.bsubst, denote]
      exact evalIter_congr (iha s ρ ξ hs) fun x => ihb (s.up _) (ρ, x) (ξ, x) (SubstDen.up P γ hs _ x)

end Silmaril.Isotope.LetParIter.Proofs
