module

public import Silmaril.SSA.LambdaRTL.CFG.Lexical.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Thms
public import Silmaril.SSA.LambdaRTL.Version.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Lexical

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [Monad M] [LawfulMonad M] [DecidableEq V] [DecidableEq K]

/-- Reading a forward graph back into lexical regions commutes with direct
execution on the flat block list. -/
theorem runSSA_eq_evalSSA (graph : CFG V K F) (model : Model F M α) (input : V → α) :
    graph.runSSA model input = graph.toRegion.evalSSA model input :=
  Proofs.SSA.LambdaRTL.CFG.runSSA_eq_evalSSA graph model input

/-- When the readback satisfies the no-clobber condition, mutable and lexical
execution of the same graph give the same exit and payload. -/
theorem runSSA_eq_obs_of_noClobber (graph : CFG V K F) (model : Model F M α)
    (safe : graph.toRegion.NoClobber) (input : V → α) :
    graph.runSSA model input = obs <$> graph.run model input := by
  rw [runSSA_eq_evalSSA, run_eq_toRegion, ← Region.evalObs_eq_evalSSA model safe]
  rfl

/-- In particular, the observation agrees for any dominance-scoped SSA readback. -/
theorem runSSA_eq_obs_of_isSSA (graph : CFG V K F) (model : Model F M α)
    {context : Finset V} (dominance : graph.toRegion.IsSSA context) (input : V → α) :
    graph.runSSA model input = obs <$> graph.run model input :=
  runSSA_eq_obs_of_noClobber graph model (Region.noClobber_of_isSSA dominance) input

/-- A forward target whose readback is the versioned source implements the
mutable source graph. The input to the source is taken from version zero. -/
theorem runSSA_eq_obs_of_versioned (source : CFG V K F) (target : CFG (V × Nat) K F)
    (versioned : target.toRegion = Version.versionTop source.toRegion)
    (model : Model F M α) (pairs : model.PairLawful) (input : V × Nat → α) :
    target.runSSA model input = obs <$> source.run model (fun x => input (x, 0)) := by
  rw [runSSA_eq_evalSSA, versioned, Version.versionTop_evalSSA model pairs _ _ input (fun _ => rfl),
    run_eq_toRegion]
  rfl

end Silmaril.SSA.LambdaRTL.CFG
