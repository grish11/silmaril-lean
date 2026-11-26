module

public import Silmaril.SSA.Isotope.LetIter.Thms
public import Silmaril.Semantics.Elgot.Parallel.Defs

/-! # The product and feedback operations for LetParIter interpretation -/

@[expose] public section

namespace Silmaril.Isotope.Parallel

open LetIter.ProofRelevant.Semantics

universe u v

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {m : Type v → Type v} [Monad m] {A B : τ}

/-- Interpret the ordered result of independent branches using the same
chosen product as native LetIter. -/
def evalPar (P : Elgot.ParallelPairing m) (x : m (TyDen A)) (y : m (TyDen B)) :
    m (TyDen (product A B)) :=
  (TypeModel.productEquiv A B).symm <$> P.pair x y

/-- Interpret a native-shaped iteration: the seed runs once and the body either
returns on the left or supplies the next state on the right. -/
def evalIter [Elgot.Iterate m] (seed : m (TyDen A))
    (step : TyDen A → m (TyDen (coprod B A))) : m (TyDen B) :=
  seed >>= Elgot.iter (fun a => step a >>= fun s => pure (TypeModel.coprodEquiv B A s))

end Silmaril.Isotope.Parallel
