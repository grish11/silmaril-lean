module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.EntryLet.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms

/-! # Entry-let sequencing from the one-block native law -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.CfgEta
open Silmaril.DeBruijn (lift)

universe u v

variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]

private theorem let_br_lsubst (a : Tm Φ) (d : Region Φ) :
    (Region.let₁ a (.br 0 (.var 0))).lsubst (fun _ => d) = .let₁ a d := by
  simp only [lsubst, liftLSubstVars, substVars_renameVars]
  have h : Tm.singleSubst (.var 0 : Tm Φ) ∘ lift Nat.succ = Tm.var := by
    funext i
    cases i <;> rfl
  rw [h, substVars_var]

/-- Entry-let sequencing is an instance of the existing one-block law. -/
theorem entryLet_of_le_one {n : Nat} (hn : n ≤ 1) : EntryLet (Eqv (τ := τ) (Φ := Φ)) n := by
  rcases n with _ | _ | n
  · intro Γ L S a d blocks R ha hd hb
    exact (Eqv.native (.base (.entry (.cfgZero (.let₁ ha hd.hasType) blocks)))).trans
      (Eqv.let₁ ha (Eqv.native (.base (.entry (.cfgZero hd.hasType _)))).symm)
  · intro Γ L S a d blocks R ha hd hb
    have same : blocks = fun _ => blocks 0 := funext fun i => congrArg blocks (Fin.eq_zero i)
    rw [same]
    have hd' : ValueBranches (S :: Γ) d (R 0 :: L) := hd
    have hb' : ValueBranches (R 0 :: Γ) (blocks 0) (R 0 :: L) := hb 0
    have seq := seqCont (.let₁ ha (.br (ℓ := 0) rfl (.var (i := 0) rfl))) hd' hb'
    simpa only [let_br_lsubst, singleCfg] using seq
  · omega

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta
