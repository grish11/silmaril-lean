module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.LiveOut

/-! # Effect-preserving observation of the exit store projection -/

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut

open Silmaril.Elgot

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

/-- The explicit store reads evaluate to the selected tuple. -/
theorem reads_eval (model : Model F M α) (σ : V → α) (fields : List V) :
    (reads fields).eval model σ = Version.packVal model σ fields :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.LiveOut.reads_eval model σ fields

variable [Monad M] [LawfulMonad M] [DecidableEq V] [DecidableEq K]

/-- The mapped transfer changes only the eventual exit payload. A hit
executes the original body with the original argument and store. -/
theorem step_commutes (model : Model F M α) (fields : K → List V) (graph : CFG V K F)
    (pending : Transfer V K α) :
    Sum.map (project model fields) (encode model fields graph) <$> Cyclic.step model graph.blocks pending =
      Cyclic.step model (attach fields graph).blocks (encode model fields graph pending) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.LiveOut.step_commutes model fields graph pending

/-- Reading live-outs at the exiting branches preserves the complete
execution and computes the projection of its actual final mutable store. -/
theorem run_project [Iterate M] [LawfulElgotMonad M] (model : Model F M α)
    (fields : K → List V) (graph : CFG V K F) (σ : V → α) :
    Cyclic.run model (attach fields graph) σ = project model fields <$> Cyclic.run model graph σ :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.LiveOut.run_project model fields graph σ

/-- The actual versioner reads the newly explicit uses at their current
versions. Even write-only registers in the original CFG are included when
the new exit reads require them. -/
theorem versioned_run_project [Iterate M] [LawfulElgotMonad M]
    (model : Model F M α) (pairs : model.PairLawful) (fields : K → List V)
    (graph : CFG V K F) (input : V × Nat → α) :
    Cyclic.runSSA model (Versioning.compile (attach fields graph)) input =
      (obs ∘ project model fields) <$> Cyclic.run model graph (fun reg => input (reg, 0)) := by
  rw [← Versioning.run_commutes model pairs, run_project]
  simp only [map_eq_pure_bind, bind_assoc, pure_bind, Function.comp_apply]

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut
