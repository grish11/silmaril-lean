module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Version

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Versioning

open Silmaril.Elgot

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq V] [DecidableEq K]

/-- The compiled entry is SSA with the supported version-zero inputs. -/
theorem compile_entry_isSSA (graph : CFG V K F) :
    (compile graph).entry.toRegion.IsSSA ((registers graph).map fun reg => (reg, 0)).toFinset :=
  Proofs.SSA.LambdaRTL.CFG.CyclicVersion.compile_entry_isSSA graph

/-- Each target block is SSA in the singleton context of its packet parameter.
Version names are local to a block invocation. -/
theorem compile_blocks_areSSA (graph : CFG V K F) (item : K × Block (V × Nat) K F)
    (member : item ∈ (compile graph).blocks) : item.2.body.toRegion.IsSSA {item.2.param} :=
  Proofs.SSA.LambdaRTL.CFG.CyclicVersion.compile_blocks_areSSA graph item member

variable [Monad M] [LawfulMonad M]

/-- The entry, executed against version-zero inputs, emits the encoded transfer. -/
theorem entry_commutes (model : Model F M α) (pairs : model.PairLawful) (graph : CFG V K F)
    (input : V × Nat → α) :
    encode model graph <$> enter model graph (fun reg => input (reg, 0)) =
      (compile graph).entry.evalJump model input :=
  Proofs.SSA.LambdaRTL.CFG.CyclicVersion.entry_commutes model pairs graph input

/-- A named step preserves effects. On a hit, the resulting transfer is encoded
for its next destination. On a miss, the observed exit and payload coincide. -/
theorem step_commutes (model : Model F M α) (pairs : model.PairLawful) (graph : CFG V K F)
    (input : V × Nat → α) (transfer : Transfer V K α) :
    Sum.map obs (encode model graph) <$> step model graph.blocks transfer =
      Cyclic.stepSSA model (compile graph).blocks input (encode model graph transfer) :=
  Proofs.SSA.LambdaRTL.CFG.CyclicVersion.step_commutes model pairs graph input transfer

/-- The generated lexical table has the mutable graph's exit and payload in
every lawful Elgot model with the pair law. -/
theorem run_commutes [Iterate M] [LawfulElgotMonad M]
    (model : Model F M α) (pairs : model.PairLawful) (graph : CFG V K F)
    (input : V × Nat → α) :
    obs <$> Cyclic.run model graph (fun reg => input (reg, 0)) =
      Cyclic.runSSA model (compile graph) input :=
  Proofs.SSA.LambdaRTL.CFG.CyclicVersion.run_commutes model pairs graph input

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Versioning
