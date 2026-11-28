module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.InstructionMap

/-! # Primitive relabelling for named cyclic tables and runners -/

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic

open Silmaril.Elgot

universe v w
variable {V K : Type w} {F G : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq K]

/-- Opcode relabelling preserves first-match lookup, including misses. -/
theorem lookup_mapOp (f : F → G) (table : List (K × Block V K F)) (label : K) :
    (table.map fun item => (item.1, item.2.mapOp f)).lookup label =
      (table.lookup label).map (Block.mapOp f) :=
  Proofs.SSA.LambdaRTL.CFG.CyclicRenaming.lookup_mapOp f table label

variable [DecidableEq V] [Monad M] [LawfulMonad M] [Iterate M]

/-- Reducing the primitive model preserves the mutable run with its final store. -/
theorem run_mapOp (f : F → G) (model : Model G M α) (graph : CFG V K F) (store : V → α) :
    Cyclic.run model (graph.mapOp f) store = Cyclic.run (model.reduct f) graph store :=
  Proofs.SSA.LambdaRTL.CFG.CyclicRenaming.run_mapOp f model graph store

/-- The same primitive reduct preserves lexical execution. -/
theorem runSSA_mapOp (f : F → G) (model : Model G M α) (graph : CFG V K F) (input : V → α) :
    Cyclic.runSSA model (graph.mapOp f) input = Cyclic.runSSA (model.reduct f) graph input :=
  Proofs.SSA.LambdaRTL.CFG.CyclicRenaming.runSSA_mapOp f model graph input

end Silmaril.SSA.LambdaRTL.CFG.Cyclic
