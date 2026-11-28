module

public import Silmaril.SSA.Isotope.LetParIter.Semantics.Defs

public section

namespace Silmaril.Isotope.Parallel.Proofs

open LetIter.ProofRelevant.Semantics

universe u v

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Elgot.Iterate m]
  [Elgot.LawfulElgotMonad m] {A B : τ}

theorem evalIter_unfold (seed : m (TyDen A)) (step : TyDen A → m (TyDen (coprod B A))) :
    evalIter seed step = (seed >>= fun a => step a >>= fun s =>
      Sum.elim pure (fun next => evalIter (pure next) step) (TypeModel.coprodEquiv B A s)) := by
  let f : TyDen A → m (TyDen B ⊕ TyDen A) :=
    fun a => step a >>= fun s => pure (TypeModel.coprodEquiv B A s)
  change (seed >>= Elgot.iter f) = _
  apply bind_congr
  intro a
  rw [congrFun (Elgot.LawfulElgotMonad.fixpoint f) a]
  simp only [f, bind_assoc, pure_bind, evalIter]

theorem evalIter_return (seed : m (TyDen A)) (result : TyDen A → TyDen B) :
    evalIter seed (fun a => pure ((TypeModel.coprodEquiv B A).symm (.inl (result a)))) =
      (result <$> seed) := by
  rw [evalIter_unfold]
  simp [bind_pure_comp]

end Silmaril.Isotope.Parallel.Proofs
