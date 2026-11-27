module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward

/-! # Forwarding registers through φ rows keeps the run

The normalized graph has the blocks of the original graph at the same
labels, the same jumps, and the same exit partition.

It runs like the original graph. The independent φ evaluator, which
reads every φ operand in the store of the predecessor, gives the
normalized graph the run of the original graph on the original part of
the input, whatever the copies hold at the start. The condition is that
no block defines a register that it receives: then the copy of a block
stays equal to the register while the block runs.

The proof follows the pending transfers. A transfer of the normalized
graph is kept when its jump is written in the original graph and the
copies of its source are equal to the registers. A kept transfer steps
as its original part does, to a kept transfer, and the two iterations are
related by the uniformity law of the iteration.

With the existing theorem for the lowering, the lexical run of the
lowered normalized graph is the φ run of the original graph.

Nothing here says which registers to forward, or that the lowered
normalized graph elaborates at given captures. Those are checked on the
graph at hand by the existing check and the existing elaborator.
-/

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward

open Silmaril.Elgot
open Silmaril.SSA.LambdaRTL (Model)
open Silmaril.SSA.LambdaRTL.CFG (Body)

universe v w

variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq V] [DecidableEq K]

/-- The normalized graph has a block exactly where the original graph has
one, and it is the normalized block. -/
theorem lookup_forward (graph : Graph V K F) (table : Table V K) (key : K) :
    (forward graph table).blocks.lookup key =
      (graph.blocks.lookup key).map (block table graph key) :=
  lookup_forward_proof graph table key

omit [DecidableEq V] [DecidableEq K] in
/-- A normalized body has the targets of the original body. -/
theorem body_targets (read : V → Name V K) (source : Body V (Option K) F) :
    (body read source).targets = source.targets :=
  body_targets_proof read source

/-- The normalized graph has the exit partition of the original graph. -/
theorem checkExits_forward (graph : Graph V K F) (table : Table V K) (exits : List (Option K)) :
    OrderedExits.checkExits (forward graph table) exits = OrderedExits.checkExits graph exits :=
  checkExits_forward_proof graph table exits

variable [Monad M] [LawfulMonad M] [Iterate M] [LawfulElgotMonad M]

/-- The normalized graph runs like the original graph on the original
part of its input, for any values of the copies, when no block defines a
register that it receives. -/
theorem run_forward (model : Model F M α) (graph : Graph V K F) (table : Table V K)
    (ok : check graph table = true) (input : Name V K → α) :
    OrderedExits.run model (forward graph table) input =
      OrderedExits.run model graph (input ∘ Sum.inl) :=
  run_forward_proof model graph table ok input

/-- The lexical run of the lowered normalized graph is the φ run of the
original graph. -/
theorem run_lowered (model : Model F M α) (pairs : model.PairLawful) (graph : Graph V K F)
    (table : Table V K) (ok : check graph table = true) (input : Name V K → α) :
    Cyclic.runSSA model (Versioning.compile (OrderedExits.lower (forward graph table)))
        (inputEnv model input) =
      OrderedExits.run model graph (input ∘ Sum.inl) :=
  (OrderedExits.run_commutes model pairs (forward graph table) input).symm.trans
    (run_forward model graph table ok input)

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward
