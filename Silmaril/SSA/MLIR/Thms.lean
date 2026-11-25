module

public import Silmaril.SSA.MLIR.Defs
public import Silmaril.SSA.MLIR.Arith.LetIter.Thms
public import Silmaril.SSA.MLIR.Module.Thms
import Silmaril.Proofs.SSA.MLIR.Observations

/-! The public entry point for typed function modules, scalar blocks, and
their checked lowerings and observations. -/

public section

universe v s

namespace Silmaril.MLIR.Arith

open Silmaril.Isotope.Institution.Observational
open Silmaril.Isotope.Morphism

variable {Γ : List Width} {w : Width}

/-- At a typed input, the only LambdaSSA observation is a return of the
source result at exit zero. -/
theorem Block.toLambdaSSA_observations (block : Block Γ w) (env : Env Γ) :
    ssaBeh 1 env.observationModel block.toScopedLambdaSSA =
      {Observation.ret () (0, word (block.denote env)) ()} :=
  Proofs.MLIR.Arith.toLambdaSSA_observations block env

/-- The same observation in LetIter, with the single exit tag removed. -/
theorem Block.toLetIter_observations (block : Block Γ w) (env : Env Γ) :
    iterBeh env.observationModel block.toLetIter =
      {Observation.ret () (word (block.denote env)) ()} :=
  (iterBeh_encodeSingle env.observationModel block.toScopedLambdaSSA).trans
    ((congrArg (Set.image (Observation.mapValue Prod.snd))
      (block.toLambdaSSA_observations env)).trans Set.image_singleton)

/-- The existing single-exit quotient isomorphism sends the LambdaSSA
class of this lowering to its LetIter class. -/
theorem Block.toLetIter_quotEquiv (block : Block Γ w) :
    SSAIter.quotEquiv (Quotient.mk (SSAIter.regionSetoid.{0, v, s} Prim 1 Γ.length)
      block.toScopedLambdaSSA) =
    Quotient.mk (SSAIter.termSetoid.{0, v, s} Prim Γ.length) block.toLetIter :=
  rfl

end Silmaril.MLIR.Arith
