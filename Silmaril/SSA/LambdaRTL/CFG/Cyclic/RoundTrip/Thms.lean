module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.RoundTrip

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Versioning

open Silmaril.Elgot

universe v w

variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq V] [DecidableEq K] [Infinite V]
  [Monad M] [LawfulMonad M] [Iterate M] [LawfulElgotMonad M]

/-- The reconstructed mutable graph agrees with the source on the whole
Elgot computation of the exit label and payload, at the same initial store.
The pair law justifies packet decoding, and the infinite name supply gives
fresh names for the finitely many nonzero versions. -/
theorem roundTrip_run_obs (model : Model F M α) (pairs : model.PairLawful)
    (graph : CFG V K F) (store : V → α) :
    obs <$> Cyclic.run model (roundTrip graph) store = obs <$> Cyclic.run model graph store :=
  Proofs.SSA.LambdaRTL.CFG.CyclicRoundTrip.roundTrip_run_obs model pairs graph store

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Versioning
