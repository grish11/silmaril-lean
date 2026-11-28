module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Prune.Correctness

/-! The dispatcher inherits both branches' typed routing and observation laws. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune

open Diamond.SCCP (TupleCovers)
open PruneExit (InputFacts)
open SeaOfNodes.MLIR (sourceInputs)
open Loop.MLIR.CF (TargetOp evalOp model)
open Loop.MLIR.CF.Bank (Label Values bankEnv lower)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

variable {Γ carried : List Width} {result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs} {facts : InputFacts Γ}
variable {input : Env Γ} {cfg : Cfg TargetOp (Label carried result) Γ [result]}

/-- An admitted output is exactly the output of one of the existing checked passes. -/
theorem rewrite_eq_some_iff :
    rewrite g facts = some cfg ↔
      PruneExit.Bank.rewrite g facts = some cfg ∨ PruneInfeasibleExit.rewrite g facts = some cfg :=
  Proofs.rewrite_eq_some_iff

/-- The dispatcher refuses exactly when both tail marks agree. -/
theorem rewrite_eq_none_iff :
    rewrite g facts = none ↔
      (incomingIndex .backedge ∈ (solve model g facts).1 ↔ exitIndex ∈ (solve model g facts).1) :=
  Proofs.rewrite_eq_none_iff

/-- Even when the exit is unreachable, the emitted CFG retains its exit block. -/
theorem blocks_eq (rewritten : rewrite g facts = some cfg) :
    cfg.entry = (lower g).entry ∧ cfg.block .exit = (lower g).block .exit :=
  Proofs.blocks_eq rewritten

/-- The chosen label and its full typed payload agree at every covered arrival. -/
theorem arrives_frame (rewritten : rewrite g facts = some cfg) (covered : TupleCovers facts (sourceInputs input))
    {via : Incoming} {count : Nat} {old : Values carried}
    (arrived : Arrives model g (sourceInputs input) via count old) :
    (cfg.block .header).eval evalOp (fun term env => term.eval env) ((bankEnv old).append input) =
      ((lower g).block .header).eval evalOp (fun term env => term.eval env) ((bankEnv old).append input) :=
  Proofs.arrives_frame rewritten covered arrived

theorem run_eq (rewritten : rewrite g facts = some cfg) (covered : TupleCovers facts (sourceInputs input))
    (fuel : Nat) : cfg.run evalOp fuel input = (lower g).run evalOp fuel input :=
  (rewrite_eq_some_iff.mp rewritten).elim
    (fun exits => PruneExit.Bank.run_eq exits covered fuel)
    (fun feedback => PruneInfeasibleExit.run_eq feedback covered fuel)

/-- The emitted partial observation includes the exact return tuple or undefinedness. -/
theorem denotePart_eq (rewritten : rewrite g facts = some cfg) (covered : TupleCovers facts (sourceInputs input)) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed cfg).denotePart evalOp input =
      (g.denote model (sourceInputs input)).map (fun value => Outcome.returned (.cons value .nil)) :=
  (rewrite_eq_some_iff.mp rewritten).elim
    (fun exits => PruneExit.Bank.denotePart_eq exits covered)
    (fun feedback => PruneInfeasibleExit.denotePart_eq feedback covered)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune
