module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.MLIR.CF.SwitchAssert (Cfg)
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input : List Width} {carried result saved : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {index : Nat} {cut : Point (SourceLabel carried result)} {output : Output Input carried result}

/-- A synthesized cut is legal in the CFG read by the chooser. -/
theorem chooseCfgCut?_sound
    {cfg : Silmaril.MLIR.CF.Cfg TargetOp (SourceLabel carried result) Input [result]}
    {operands : List (Point (SourceLabel carried result))} {uses : List (Use (SourceLabel carried result))}
    (selected : chooseCfgCut? cfg operands uses = some cut) :
    cut ∈ candidateCuts cfg blocks ∧ Legal cfg operands uses cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.chooseCfgCut?_sound selected

/-- The synthesized corridor drives the same emitter and returns the same
result as the existing hoist with the synthesized complete tree. -/
theorem pickAndHoist?_eq :
    pickAndHoist? g index = (synthesizedTree? g).bind fun tree =>
      pickBindingAndHoist? g tree.1 index :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.pickAndHoist?_eq

/-- A chosen cut outside the preheader insertion point is refused. -/
theorem refuses_otherCut {binding : Binding Input (carried :: Input) saved carried result}
    (found : findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩)
    (selected : chooseCut? g binding.operands binding.uses = some cut)
    (outside : cut ≠ ⟨none, 0⟩) : pickAndHoist? g index = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.refuses_otherCut found selected outside

/-- A successful move uses the synthesized corridor cut for the actual
nominated definition and its exact operand and use sites. -/
theorem pickAndHoist?_placement (picked : pickAndHoist? g index = some (cut, output)) :
    cut = ⟨none, 0⟩ ∧ cut ∈ candidateCuts (lower g) blocks ∧
      ∃ binding : Binding Input (carried :: Input) output.1 carried result,
        findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨output.1, binding⟩ ∧
        chooseCut? g binding.operands binding.uses = some cut ∧
        Legal (lower g) binding.operands binding.uses cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.pickAndHoist?_placement picked

/-- The preheader value is computed from captured inputs and routed through
entry and feedback. The original exit transfer is preserved. -/
theorem pickAndHoist?_routes (picked : pickAndHoist? g index = some (cut, output))
    (input : Env Input) :
    ∃ (binding : Binding Input (carried :: Input) output.1 carried result)
      (operands : Operands Input binding.args),
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨output.1, binding⟩ ∧
      binding.captured? = some operands ∧
      Routes (lower g) output.2 input (evalOp binding.op (operands.eval input)) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.pickAndHoist?_routes picked input

theorem pickAndHoist?_run_eq (picked : pickAndHoist? g index = some (cut, output))
    (input : Env Input) (fuel : Nat) :
    output.2.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.pickAndHoist?_run_eq picked input fuel

/-- Fuel `budget + 3` retains the native backedge-budget observation. -/
theorem pickAndHoist?_budget (picked : pickAndHoist? g index = some (cut, output))
    (input : Env Input) (budget : Nat) :
    output.2.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.pickAndHoist?_budget picked input budget

/-- The partial CFG observation agrees, including undefinedness. -/
theorem pickAndHoist?_denotePart (picked : pickAndHoist? g index = some (cut, output))
    (input : Env Input) :
    (Cfg.embed output.2).denotePart evalOp input = (Cfg.embed (lower g)).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.pickAndHoist?_denotePart picked input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
