module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Defs

/-! # Moving a typed let past a local CFG binder -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta

open Silmaril.DeBruijn (lift)

universe u v

variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]

/-- The exact law for moving an entry let ahead of a CFG of arity `n`.
The local blocks are weakened past the new let binder. -/
def EntryLet (E : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) (n : Nat) : Prop :=
  ∀ {Γ : VCtx τ} {L : LCtx τ} {S : τ} {a : Tm Φ} {d : Region Φ}
      {blocks : Fin n → Region Φ} (R : Fin n → τ),
    Tm.HasType Γ a S →
    ValueBranches (S :: Γ) d (List.ofFn R ++ L) →
    (∀ i, ValueBranches (R i :: Γ) (blocks i) (List.ofFn R ++ L)) →
    E Γ (.cfg (.let₁ a d) n blocks)
      (.let₁ a (.cfg d n (fun i => (blocks i).renameVars (lift Nat.succ)))) L

end Silmaril.Isotope.LambdaSSA.Region.CfgEta
