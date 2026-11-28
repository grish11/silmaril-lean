module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms

/-! # Sequencing a returned pair and projecting the second field -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairSecondProjection

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CfgEta.TypeCategory (returnRegion returnRegion_typed singletonValueFamily)
open Paper.RetainedLet (returnOnce)
open Paper.UnaryReturn (returnOnce_valueBranches)
open Paper.UnaryReturn.Beta.Constructors (pairSequence)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

local notation "E" => Paper.Extension.Eqv Seed

omit [TypeFormers τ] in
private theorem weakSingleton {A : τ} {Γ : VCtx τ} :
    Ren [A] (A :: Γ) id := by
  intro i D h
  cases i with
  | zero => exact h
  | succ i => simp [At] at h

theorem return_pair_second
    (pair : ∀ {Γ L r s}, Paper.WithPairReturns.Step Γ r s L → Seed Γ r s L)
    (projection : ∀ {Γ L r s}, Paper.WithProjectionReturns.Step Γ r s L → Seed Γ r s L)
    {Γ : VCtx τ} {A B : τ} {a b : Tm Φ}
    (ha : Tm.HasType Γ a A) (hb : Tm.HasType Γ b B) :
    E Γ (returnRegion (.let₁ (.pair a b) (.let₂ (.var 0) (.var 0))))
      (.let₁ a (.let₁ (b.rename Nat.succ) (.br 0 (.var 0)))) [B] := by
  let pairBody := returnOnce_valueBranches (.pair ha hb)
  let seqBody := Paper.WithPairReturns.pairSequence_typed ha hb
  let hproj := Paper.WithProjectionReturns.Step.snd (Φ := Φ) A B
  have proj : E [product A B] (returnRegion (.let₂ (.var 0) (.var 0)))
      (.let₂ (.var 0) (.br 0 (.var 0))) [B] :=
    .extra hproj.valueBranches.1.hasType hproj.valueBranches.2.hasType (projection hproj)
  have projCaptured : E (product A B :: Γ) (returnRegion (.let₂ (.var 0) (.var 0)))
      (.let₂ (.var 0) (.br 0 (.var 0))) [B] := by
    simpa only [renameVars_id] using proj.renameVars (weakSingleton (A := product A B) (Γ := Γ))
  have hp : ValueBranches (product A B :: Γ) (returnRegion (.let₂ (.var 0) (.var 0))) [B] :=
    returnRegion_typed (Φ := Φ) (.let₂ (.var (i := 0) rfl) (.var (i := 0) rfl))
  have seq : E Γ (returnOnce (.pair a b)) (pairSequence a b) [product A B] :=
    .extra pairBody.hasType seqBody.hasType (pair (.seq ha hb))
  refine (seq.lsubstPost pairBody seqBody (fun _ _ hi => ((singletonValueFamily hp) hi).hasType)).trans ?_
  have comp : E Γ ((pairSequence a b).lsubst (fun _ => returnRegion (.let₂ (.var 0) (.var 0))))
      ((pairSequence a b).lsubst (fun _ => .let₂ (.var 0) (.br 0 (.var 0)))) [B] := by
    apply Paper.Extension.Eqv.lsubstCongr seqBody
    intro i T hi
    cases i with
    | zero => cases Option.some.inj hi; exact projCaptured
    | succ i => simp [At] at hi
  refine comp.trans ?_
  exact .let₁ ha (.let₁ (hb.rename (Ren.wk Γ A))
    (.paper (.productBeta (.let₂Beta (.var (i := 1) rfl) (.var (i := 0) rfl)
      (.br rfl (.var (i := 0) rfl))))))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairSecondProjection
