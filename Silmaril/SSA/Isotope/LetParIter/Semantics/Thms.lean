module

public import Silmaril.SSA.Isotope.LetParIter.Semantics.Defs
import Silmaril.Proofs.SSA.Isotope.LetParIter.Semantics

/-! # Iteration in the parallel language -/

public section

namespace Silmaril.Isotope.Parallel

open LetIter.ProofRelevant.Semantics

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {m : Type v → Type v} [Monad m] [Elgot.Iterate m]
variable {A B : τ}

/-- Iteration is a context in both arguments, with the same value passed to the
two step interpretations. -/
theorem evalIter_congr {seed seed' : m (TyDen A)}
    {step step' : TyDen A → m (TyDen (coprod B A))}
    (hs : seed = seed') (hb : ∀ a, step a = step' a) :
    evalIter seed step = evalIter seed' step' := by
  rw [hs, funext hb]

/-- This is exactly the feedback clause of the native proof-relevant evaluator. -/
theorem denote_letIter_iter
    {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
    {ε : Type r} [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε m]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : LetIter.LocallyNameless.Tm ν Φ n} {b : LetIter.LocallyNameless.Tm ν Φ (n + 1)}
    (ha : LetIter.ProofRelevant.LocallyNameless.HasType Φ Γ β a A)
    (hb : LetIter.ProofRelevant.LocallyNameless.HasType Φ Γ (.snoc β A) b (coprod B A))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (ε := ε) (m := m) (.iter ha hb) γ ρ =
      evalIter (denote (ε := ε) ha γ ρ) (fun s => denote (ε := ε) hb γ (ρ, s)) := by
  rw [denote, evalIter]

variable [LawfulMonad m] [Elgot.LawfulElgotMonad m]

/-- Ordinary Elgot unfolding applies even when seed or body contains parallel
pairing, because it uses only the chosen iteration. -/
theorem evalIter_unfold (seed : m (TyDen A)) (step : TyDen A → m (TyDen (coprod B A))) :
    evalIter seed step = (seed >>= fun a => step a >>= fun s =>
      Sum.elim pure (fun next => evalIter (pure next) step) (TypeModel.coprodEquiv B A s)) :=
  Proofs.evalIter_unfold seed step

/-- A body that returns immediately applies its pure result map to the seed. -/
theorem evalIter_return (seed : m (TyDen A)) (result : TyDen A → TyDen B) :
    evalIter seed (fun a => pure ((TypeModel.coprodEquiv B A).symm (.inl (result a)))) =
      (result <$> seed) :=
  Proofs.evalIter_return seed result

end Silmaril.Isotope.Parallel
