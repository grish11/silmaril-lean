module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.EntryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms

/-! # Opt-in entry-let sequencing for Paper -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet

open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The typed entry-let schema at arbitrary arity. The entry and local
blocks have constructor-valued branches. The initializer can be any
well-typed term. Each block is weakened past the new entry capture. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | seq {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {S : τ} {a : Tm Φ} {d : Region Φ}
      {blocks : Fin n → Region Φ} (R : Fin n → τ)
      (ha : Tm.HasType Γ a S)
      (hd : ValueBranches (S :: Γ) d (List.ofFn R ++ L))
      (hb : ∀ i, ValueBranches (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
      Step Γ (.cfg (.let₁ a d) n blocks)
        (.let₁ a (.cfg d n (fun i => (blocks i).renameVars (lift Nat.succ)))) L

abbrev Eqv := Extension.Eqv (Step (τ := τ) (Φ := Φ))

abbrev TypeCategory := Extension.Singleton.TypeCategory (Step (τ := τ) (Φ := Φ))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet
