module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.WellFormed.Thms

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits

open Silmaril.Elgot

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq V] [DecidableEq K] [Monad M]

omit [Monad M] in
/-- An accepted table certifies the scope of internal edge operands and
external payload reads through the existing φ arrival checker. -/
theorem check_scope (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    (certificate : GlobalSSA.Certificate V K) (checked : check graph exits inputs certificate = true) :
    GlobalSSA.WellFormed (forScope graph exits) inputs := by
  simp only [check, Bool.and_eq_true] at checked
  exact GlobalSSA.check_sound checked.2

/-- The caller's predecessor selects the column before any destinations are written. -/
theorem step_internal (model : Model F M α) (graph : Graph V K F) (pred target : Option K)
    (value : α) (store : V → α) {block : Block V K F} (found : lookup graph target = some block) :
    step model graph (pred, target, value, store) =
      Sum.inr <$> execute model target block.body (assign model pred store block.rows store) := by
  simp [step, found]

variable [LawfulMonad M] [Iterate M] [LawfulElgotMonad M]

/-- The independent predecessor-snapshot evaluator agrees with the actual
lexical runner, preserving the label and payload of each external exit. -/
theorem run_commutes (model : Model F M α) (pairs : model.PairLawful)
    (graph : Graph V K F) (input : V → α) :
    run model graph input =
      Cyclic.runSSA model (Versioning.compile (lower graph)) (inputEnv model input) :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicPhi.OrderedExits.run_commutes model pairs graph input

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits
