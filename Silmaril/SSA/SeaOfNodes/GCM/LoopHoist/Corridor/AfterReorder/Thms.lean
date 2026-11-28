module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.MLIR.CF.SwitchAssert (Cfg)
open Header.Sequence (State)
open Loop.MLIR.CF (Program evalOp lower model)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {output : Output Input carried result}
variable {plan : Plan} {priorities : List Nat} {origin : Nat}

/-- The tracked result exposes the exact resolution and cut consumed by the emitter. -/
theorem resolveMove?_spec {state : State Input carried result} {index : Nat}
    {cut : Point (SourceLabel carried result)}
    (accepted : resolveMove? state origin = some (index, cut, output)) :
    Header.Priority.resolve? state origin = some index ∧
      hoistCodeWith? state.cfg.entry (state.cfg.block .header) index (chooseCfgCut? state.cfg) =
        some (cut, output) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.resolveMove?_spec accepted

/-- The emitted CFG is exactly the result of replaying the returned plan. -/
theorem schedule?_replay (accepted : schedule? g priorities origin = some (plan, output)) :
    replay? g plan = some output :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.schedule?_replay accepted

/-- The original identity resolves on the reordered CFG, where its
exact operand origins and use occurrences admit preheader cut zero. -/
theorem replay?_placement (emitted : replay? g plan = some output) :
    ∃ (state : State Input carried result) (index : Nat)
      (binding : Binding Input (carried :: Input) output.1 carried result),
      Header.Sequence.run? (Header.Sequence.initial (lower g)) plan.header = some state ∧
      state.origins[index]? = some plan.hoistOrigin ∧
      findBinding index 0 headerOrigins (state.cfg.block .header) = some ⟨output.1, binding⟩ ∧
      chooseCfgCut? state.cfg binding.operands binding.uses = some ⟨none, 0⟩ ∧
      Legal state.cfg binding.operands binding.uses ⟨none, 0⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.replay?_placement emitted

/-- Entry and feedback carry the captured result along with the original
latch. Exit carries the reordered CFG's exact original exit value. -/
theorem replay?_routes (emitted : replay? g plan = some output) (input : Env Input) :
    ∃ (state : State Input carried result) (index : Nat)
      (binding : Binding Input (carried :: Input) output.1 carried result)
      (operands : Operands Input binding.args),
      Header.Sequence.run? (Header.Sequence.initial (lower g)) plan.header = some state ∧
      state.origins[index]? = some plan.hoistOrigin ∧
      findBinding index 0 headerOrigins (state.cfg.block .header) = some ⟨output.1, binding⟩ ∧
      binding.captured? = some operands ∧
      Routes state.cfg output.2 input (evalOp binding.op (operands.eval input)) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.replay?_routes emitted input

/-- Both steps preserve one transition per CFG block. -/
theorem replay?_run_eq (emitted : replay? g plan = some output) (input : Env Input) (fuel : Nat) :
    output.2.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.replay?_run_eq emitted input fuel

theorem replay?_budget (emitted : replay? g plan = some output) (input : Env Input) (budget : Nat) :
    output.2.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.replay?_budget emitted input budget

theorem replay?_denotePart (emitted : replay? g plan = some output) (input : Env Input) :
    (Cfg.embed output.2).denotePart evalOp input = (Cfg.embed (lower g)).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.replay?_denotePart emitted input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder
