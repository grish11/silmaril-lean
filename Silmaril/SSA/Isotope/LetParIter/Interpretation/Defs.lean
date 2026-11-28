module

public import Silmaril.SSA.Isotope.LetParIter.Defs

/-! # Monadic interpretation of exact LetParIter typing -/

@[expose] public section

namespace Silmaril.Isotope.LetParIter

open Parallel LetIter.ProofRelevant.Semantics

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [Elgot.Iterate m] [InstructionModel Φ τ ε m]

/-- The native clauses retain their evaluation order. Both parallel branches
receive the same ambient values, and the supplied pairing interprets their effects. -/
def denote (P : Elgot.ParallelPairing m) {Γ : Ctx ν τ} :
    {n : Nat} → {β : BoundCtx τ n} → {a : Tm ν Φ n} → {A : τ} →
    Derivation Φ Γ β a A → CtxDen Γ → BoundDen β → m (TyDen A)
  | _, _, _, _, .fv h, γ, _ => pure (CtxDen.lookup γ _ h)
  | _, _, _, _, .bv, _, ρ => pure (BoundDen.get ρ _)
  | _, _, _, _, .op ha, γ, ρ => denote P ha γ ρ >>= denoteInstr (ε := ε) _
  | _, _, _, _, .let₁ ha hb, γ, ρ => denote P ha γ ρ >>= fun a => denote P hb γ (ρ, a)
  | _, _, _, _, .unit, _, _ => pure (TypeModel.unitEquiv.symm ())
  | _, _, _, _, .pair ha hb, γ, ρ =>
      denote P ha γ ρ >>= fun a => denote P hb γ ρ >>= fun b =>
        pure ((TypeModel.productEquiv _ _).symm (a, b))
  | _, _, _, _, .let₂ ha hb, γ, ρ => denote P ha γ ρ >>= fun ab =>
      let p := TypeModel.productEquiv _ _ ab
      denote P hb γ ((ρ, p.1), p.2)
  | _, _, _, _, .inl ha, γ, ρ =>
      denote P ha γ ρ >>= fun a => pure ((TypeModel.coprodEquiv _ _).symm (.inl a))
  | _, _, _, _, .inr hb, γ, ρ =>
      denote P hb γ ρ >>= fun b => pure ((TypeModel.coprodEquiv _ _).symm (.inr b))
  | _, _, _, _, .case he hl hr, γ, ρ => denote P he γ ρ >>= fun e =>
      match TypeModel.coprodEquiv _ _ e with
      | .inl a => denote P hl γ (ρ, a)
      | .inr b => denote P hr γ (ρ, b)
  | _, _, _, _, .abort ha, γ, ρ =>
      denote P ha γ ρ >>= fun z => Empty.elim (TypeModel.emptyEquiv z)
  | _, _, _, _, .iter ha hb, γ, ρ =>
      evalIter (denote P ha γ ρ) (fun a => denote P hb γ (ρ, a))
  | _, _, _, _, .par ha hb, γ, ρ => evalPar P (denote P ha γ ρ) (denote P hb γ ρ)
termination_by structural _ _ _ _ d _ _ => d

end Silmaril.Isotope.LetParIter
