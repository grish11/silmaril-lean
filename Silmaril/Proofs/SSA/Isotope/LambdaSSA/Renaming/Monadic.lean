module

public import Silmaril.SSA.Isotope.LambdaSSA.Renaming.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Monadic.Thms

public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Monadic

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Elgot

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]

@[simp] theorem Env.rename_get_proof {Γ Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) (δ : Env Δ) (i : Nat) {A : τ}
    (h : LambdaSSA.At Γ i A) :
    Env.get (Env.rename hρ δ) i h = Env.get δ (ρ i) (hρ h) := by
  induction Γ generalizing i ρ with
  | nil => simp [LambdaSSA.At] at h
  | cons B Γ ih =>
      cases i with
      | zero =>
          have e : B = A := by simpa [LambdaSSA.At] using h
          subst A
          rfl
      | succ i =>
          simpa [Env.rename, Env.get] using
            ih (hρ := fun ⦃j C⦄ hj => hρ (i := j + 1)
              (by simpa [LambdaSSA.At] using hj)) i
              (by simpa [LambdaSSA.At] using h)

@[simp] theorem Env.rename_lift_proof {Γ Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) (δ : Env Δ) (A : τ) (a : TyDen A) :
    Env.rename (hρ.lift A) (δ, a) = (Env.rename hρ δ, a) := by
  apply Prod.ext
  · induction Γ generalizing ρ with
    | nil => rfl
    | cons B Γ ih =>
        apply Prod.ext
        · exact ih (fun ⦃i C⦄ hi => hρ (i := i + 1)
            (by simpa [LambdaSSA.At] using hi))
        · rfl
  · rfl

variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m]
variable [InstructionModel Φ τ ε m]

/-- Term denotation is contravariantly natural in its variable context. -/
theorem Denotes.renameVars_proof {Γ Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) {a : LambdaSSA.Tm Φ} {A : τ}
    {ha : LambdaSSA.Tm.HasType Γ a A} {f : Env Γ → m (TyDen A)}
    (d : Denotes ε ha f) :
    Denotes ε (ha.rename hρ) (fun δ => f (Env.rename hρ δ)) := by
  induction d generalizing Δ ρ with
  | var h => simpa using Denotes.var (m := m) (ε := ε) (hρ h)
  | op d ih => exact .op (ih hρ)
  | let₁ da db iha ihb =>
      convert Denotes.let₁ (iha hρ) (ihb (hρ.lift _)) using 1 <;> try rfl
      funext δ
      apply bind_congr
      intro a
      rw [Env.rename_lift_proof]
  | pair da db iha ihb => exact .pair (iha hρ) (ihb hρ)
  | unit => exact .unit
  | let₂ da db iha ihb =>
      convert Denotes.let₂ (iha hρ) (ihb ((hρ.lift _).lift _)) using 1 <;> try rfl
      funext δ
      apply bind_congr
      intro ab
      dsimp only
      let p := TypeModel.productEquiv _ _ ab
      apply congrArg
      exact ((Env.rename_lift_proof (hρ.lift _) (δ, p.1) _ p.2).trans
        (congrArg (fun z => (z, p.2)) (Env.rename_lift_proof hρ δ _ p.1))).symm
  | inl d ih => exact .inl (ih hρ)
  | inr d ih => exact .inr (ih hρ)
  | case de dl dr ihe ihl ihr =>
      convert Denotes.case (ihe hρ) (ihl (hρ.lift _)) (ihr (hρ.lift _)) using 1 <;> try rfl
      funext δ
      apply bind_congr
      intro e
      cases TypeModel.coprodEquiv _ _ e with
      | inl x =>
          simp only
          apply congrArg
          exact (Env.rename_lift_proof hρ δ _ x).symm
      | inr x =>
          simp only
          apply congrArg
          exact (Env.rename_lift_proof hρ δ _ x).symm
  | abort d ih => exact .abort (ih hρ)

variable [Iterate m]

/-- Region denotation is contravariantly natural in its variable context. -/
theorem RegionDenotes.renameVars_proof {Γ Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) {region : LambdaSSA.Region Φ}
    {L : LambdaSSA.LCtx τ} {hr : LambdaSSA.Region.HasType Γ region L}
    {f : Env Γ → m (LabelDen L)} (d : RegionDenotes ε hr f) :
    RegionDenotes ε (hr.renameVars hρ) (fun δ => f (Env.rename hρ δ)) := by
  induction d generalizing Δ ρ with
  | br dt => exact .br (dt.renameVars_proof hρ)
  | case de dl dr ihl ihr =>
      convert RegionDenotes.case (de.renameVars_proof hρ)
        (ihl (hρ.lift _)) (ihr (hρ.lift _)) using 1 <;> try rfl
      funext δ
      apply bind_congr
      intro e
      cases TypeModel.coprodEquiv _ _ e with
      | inl x =>
          simp only
          apply congrArg
          exact (Env.rename_lift_proof hρ δ _ x).symm
      | inr x =>
          simp only
          apply congrArg
          exact (Env.rename_lift_proof hρ δ _ x).symm
  | let₁ da db ihb =>
      convert RegionDenotes.let₁ (da.renameVars_proof hρ) (ihb (hρ.lift _)) using 1 <;> try rfl
      funext δ
      apply bind_congr
      intro a
      rw [Env.rename_lift_proof]
  | let₂ da db ihb =>
      convert RegionDenotes.let₂ (da.renameVars_proof hρ)
        (ihb ((hρ.lift _).lift _)) using 1 <;> try rfl
      funext δ
      apply bind_congr
      intro ab
      dsimp only
      let p := TypeModel.productEquiv _ _ ab
      apply congrArg
      exact ((Env.rename_lift_proof (hρ.lift _) (δ, p.1) _ p.2).trans
        (congrArg (fun z => (z, p.2)) (Env.rename_lift_proof hρ δ _ p.1))).symm
  | cfgZero he hb de ih =>
      exact RegionDenotes.cfgZero (he.renameVars hρ)
        (fun i => (hb i).renameVars (hρ.lift _)) (ih hρ)
  | @cfg n R Γ L entry blocks he hb fe fb collective de db dc ihe ihb =>
      let fb' : ∀ i, Env (R i :: Δ) → m (LabelDen (List.ofFn R ++ L)) :=
        fun i δ => fb i (Env.rename (hρ.lift _) δ)
      let collective' : Env Δ × FiniteLabelDen R →
          m (LabelDen (List.ofFn R ++ L)) :=
        fun p => collective (Env.rename hρ p.1, p.2)
      have dc' : CollectiveDenotes Δ R L fb' collective' := by
        constructor
        intro i δ a
        simp only [collective', fb']
        rw [Env.rename_lift_proof]
        exact dc.restrict i (Env.rename hρ δ) a
      exact RegionDenotes.cfg _ _ (ihe hρ) (fun i => ihb i (hρ.lift _)) dc'

end Silmaril.Isotope.LambdaSSA.Semantics.Monadic

namespace Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Monadic

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Elgot

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]

open LambdaSSA.Semantics.Monadic (Env.rename FiniteLabelDen)

variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m]
variable [InstructionModel Φ τ ε m]

theorem Denotes.renameVars_proof {Γ Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) {a : LambdaSSA.Tm Φ} {A : τ}
    {ha : LambdaSSA.Subtyping.Tm.HasType Γ a A}
    {f : Env Γ → m (TyDen A)} (d : Denotes ε ha f) :
    Denotes ε (ha.rename hρ) (fun δ => f (LambdaSSA.Semantics.Monadic.Env.rename hρ δ)) := by
  induction d generalizing Δ ρ with
  | var h =>
      simp only [LambdaSSA.Semantics.Monadic.Env.rename_get_proof]
      exact Denotes.var (m := m) (ε := ε) (hρ h)
  | op d ih => exact .op (ih hρ)
  | let₁ da db iha ihb =>
      convert Denotes.let₁ (iha hρ) (ihb (hρ.lift _)) using 1 <;> try rfl
      funext δ
      apply bind_congr
      intro a
      rw [LambdaSSA.Semantics.Monadic.Env.rename_lift_proof]
  | pair da db iha ihb => exact .pair (iha hρ) (ihb hρ)
  | unit => exact .unit
  | let₂ da db iha ihb =>
      convert Denotes.let₂ (iha hρ) (ihb ((hρ.lift _).lift _)) using 1 <;> try rfl
      funext δ
      apply bind_congr
      intro ab
      dsimp only
      let p := TypeModel.productEquiv _ _ ab
      apply congrArg
      exact ((LambdaSSA.Semantics.Monadic.Env.rename_lift_proof (hρ.lift _) (δ, p.1) _ p.2).trans
        (congrArg (fun z => (z, p.2)) (LambdaSSA.Semantics.Monadic.Env.rename_lift_proof hρ δ _ p.1))).symm
  | inl d ih => exact .inl (ih hρ)
  | inr d ih => exact .inr (ih hρ)
  | case de dl dr ihe ihl ihr =>
      convert Denotes.case (ihe hρ) (ihl (hρ.lift _)) (ihr (hρ.lift _)) using 1 <;> try rfl
      funext δ
      apply bind_congr
      intro e
      cases TypeModel.coprodEquiv _ _ e with
      | inl x =>
          simp only
          apply congrArg
          exact (LambdaSSA.Semantics.Monadic.Env.rename_lift_proof hρ δ _ x).symm
      | inr x =>
          simp only
          apply congrArg
          exact (LambdaSSA.Semantics.Monadic.Env.rename_lift_proof hρ δ _ x).symm
  | abort d ih => exact .abort (ih hρ)
  | sub d witness ih => exact .sub (ih hρ) witness

variable [Iterate m]

theorem RegionDenotes.renameVars_proof {Γ Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) {region : LambdaSSA.Region Φ}
    {L : LambdaSSA.LCtx τ}
    {hr : LambdaSSA.Subtyping.Region.HasType Γ region L}
    {f : Env Γ → m (LabelDen L)} (d : RegionDenotes ε hr f) :
    RegionDenotes ε (hr.renameVars hρ) (fun δ => f (LambdaSSA.Semantics.Monadic.Env.rename hρ δ)) := by
  induction d generalizing Δ ρ with
  | br dt => exact .br (dt.renameVars_proof hρ)
  | case de dl dr ihl ihr =>
      convert RegionDenotes.case (de.renameVars_proof hρ)
        (ihl (hρ.lift _)) (ihr (hρ.lift _)) using 1 <;> try rfl
      funext δ
      apply bind_congr
      intro e
      cases TypeModel.coprodEquiv _ _ e with
      | inl x =>
          simp only
          apply congrArg
          exact (LambdaSSA.Semantics.Monadic.Env.rename_lift_proof hρ δ _ x).symm
      | inr x =>
          simp only
          apply congrArg
          exact (LambdaSSA.Semantics.Monadic.Env.rename_lift_proof hρ δ _ x).symm
  | let₁ da db ihb =>
      convert RegionDenotes.let₁ (da.renameVars_proof hρ) (ihb (hρ.lift _)) using 1 <;> try rfl
      funext δ
      apply bind_congr
      intro a
      rw [LambdaSSA.Semantics.Monadic.Env.rename_lift_proof]
  | let₂ da db ihb =>
      convert RegionDenotes.let₂ (da.renameVars_proof hρ)
        (ihb ((hρ.lift _).lift _)) using 1 <;> try rfl
      funext δ
      apply bind_congr
      intro ab
      dsimp only
      let p := TypeModel.productEquiv _ _ ab
      apply congrArg
      exact ((LambdaSSA.Semantics.Monadic.Env.rename_lift_proof (hρ.lift _) (δ, p.1) _ p.2).trans
        (congrArg (fun z => (z, p.2)) (LambdaSSA.Semantics.Monadic.Env.rename_lift_proof hρ δ _ p.1))).symm
  | cfgZero he hb de ih =>
      exact RegionDenotes.cfgZero (he.renameVars hρ)
        (fun i => (hb i).renameVars (hρ.lift _)) (ih hρ)
  | @cfg n R Γ L entry blocks he hb fe fb collective de db dc ihe ihb =>
      let fb' : ∀ i, Env (R i :: Δ) → m (LabelDen (List.ofFn R ++ L)) :=
        fun i δ => fb i (LambdaSSA.Semantics.Monadic.Env.rename (hρ.lift _) δ)
      let collective' : Env Δ × FiniteLabelDen R →
          m (LabelDen (List.ofFn R ++ L)) :=
        fun p => collective (LambdaSSA.Semantics.Monadic.Env.rename hρ p.1, p.2)
      have dc' : CollectiveDenotes Δ R L fb' collective' := by
        constructor
        intro i δ a
        simp only [collective', fb']
        rw [LambdaSSA.Semantics.Monadic.Env.rename_lift_proof]
        exact dc.restrict i (LambdaSSA.Semantics.Monadic.Env.rename hρ δ) a
      exact RegionDenotes.cfg _ _ (ihe hρ)
        (fun i => ihb i (hρ.lift _)) dc'

end Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Monadic
