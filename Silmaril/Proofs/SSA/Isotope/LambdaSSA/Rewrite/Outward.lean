module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheoryTyping
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Labels

/-! # Commuting a CFG out of a constructor-valued let with an outward branch -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem cfgLetBrExit {Γ : VCtx τ} {L : LCtx τ} {n ℓ : Nat} {a b : Tm Φ}
    {A B : τ} {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (hℓ : At L ℓ B)
    (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue (A :: Γ) b B)
    (hblocks : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    Region.RewriteEquiv Γ
      (.cfg (.let₁ a (.br (n + 1 + ℓ) b)) (n + 1) blocks) (.let₁ a (.br ℓ b)) L := by
  refine .trans (.cfg R (.letBr ha hb (exitAt R hℓ)) (fun i => .entry (.refl (hblocks i)))) ?_
  exact .trans (.entry (.cfgBrExit R hℓ (branchValue_singleSubst ha hb) hblocks))
    (.symm (.letBr ha hb hℓ))

theorem repaired_example :
    let r : Region Φ := .cfg (.br 1 (.var 0)) 1 (fun _ => .br 1 (.var 0))
    let s : Region Φ := .br 0 (.var 0)
    let σ : Nat → Region Φ := fun _ => .let₁ .unit (.br 0 (.var 0))
    Region.RewriteEquiv [(Silmaril.unit : τ)] (r.lsubst σ) (s.lsubst σ) [Silmaril.unit] := by
  exact cfgLetBrExit (n := 0) (ℓ := 0) (fun _ => (Silmaril.unit : τ)) rfl .unit (.var rfl)
    (fun _ => .let₁ .unit (.br (ℓ := 1) rfl (.var rfl)))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
