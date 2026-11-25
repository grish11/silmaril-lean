module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Defs
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Continuation

/-! # Label substitution and the CFG entry quotient -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA

/-- The visible entry of a region after transparent wrappers are removed. -/
private inductive EntryShape where
  | branch (label : Nat)
  | control
  | other

private def EntryShape.cfg : Nat → EntryShape → EntryShape
  | 0, shape => shape
  | n + 1, .branch ℓ => if ℓ < n + 1 then .control else .branch (ℓ - (n + 1))
  | _ + 1, _ => .control

private def entryShape {Φ : Type v} : Region Φ → EntryShape
  | .br ℓ _ => .branch ℓ
  | .cfg entry n _ => (entryShape entry).cfg n
  | _ => .other

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

private theorem entryShape_eq {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Region.CfgEquiv Γ r s L) : entryShape r = entryShape s := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ihr ihs => exact ihr.trans ihs
  | let₁ => rfl
  | let₂ => rfl
  | case => rfl
  | cfg _ _ _ ihe _ => simp only [entryShape, ihe]
  | cfgZero => rfl
  | cfgBrExit => simp [entryShape, EntryShape.cfg]
  | cfgBrLocal _ i _ _ => simp [entryShape, EntryShape.cfg, i.isLt]

theorem unitExit_not_equiv :
    ¬ Region.CfgEquiv (Φ := Φ) [(Silmaril.unit : τ)]
      (.cfg (.let₁ .unit (.br 1 (.var 0))) 1 (fun _ => .let₁ .unit (.br 1 (.var 0))))
      (.let₁ .unit (.br 0 (.var 0))) [Silmaril.unit] := by
  intro h
  have bad : EntryShape.control = EntryShape.other := entryShape_eq h
  cases bad

theorem labelSubstitution_counterexample :
    ∃ (r s : Region Φ) (σ : Nat → Region Φ),
      Region.CfgEquiv [(Silmaril.unit : τ)] r s [Silmaril.unit] ∧
      Region.LSubst.HasType [(Silmaril.unit : τ)] [Silmaril.unit] [Silmaril.unit] σ ∧
      ¬ Region.CfgEquiv [(Silmaril.unit : τ)] (r.lsubst σ) (s.lsubst σ) [Silmaril.unit] := by
  let blocks : Fin 1 → Region Φ := fun _ => .br 1 (.var 0)
  let r : Region Φ := .cfg (.br 1 (.var 0)) 1 blocks
  let s : Region Φ := .br 0 (.var 0)
  let σ : Nat → Region Φ := fun _ => .let₁ .unit (.br 0 (.var 0))
  refine ⟨r, s, σ, ?_, ?_, ?_⟩
  · exact .cfgBrExit (n := 0) (ℓ := 0) (fun _ => Silmaril.unit) rfl (.var rfl)
      (fun _ => .br (ℓ := 1) rfl (.var rfl))
  · intro ℓ A h
    exact .let₁ .unit (.br (ℓ := 0) rfl (.var rfl))
  · exact unitExit_not_equiv (τ := τ) (Φ := Φ)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
