module

public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
public import Silmaril.Semantics.ElgotMonads.Defs
import Silmaril.Proofs.SSA.MLIR.CF.SwitchAssert.Denotation

public section

namespace Silmaril.MLIR.CF.SwitchAssert

open Arith (Width Env)
open Silmaril.MLIR.Pure (Eval OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}

/-- Each iteration consumes one block of fuel, starting with the entry and
including the block that returns or aborts. Zero fuel executes no blocks. -/
theorem Cfg.runFor_eq_ofOption_run (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (fuel : Nat) (input : Env Input) :
    Elgot.Part.runFor (fun state => Part.some (cfg.step evalOp input state)) fuel
        ⟨Input, cfg.entry, input⟩ = Part.ofOption (cfg.run evalOp fuel input) :=
  Proofs.MLIR.CF.SwitchAssert.runFor_eq_ofOption_run cfg evalOp fuel input

/-- The denotation contains exactly the outcomes witnessed at finite fuel. -/
theorem Cfg.mem_denotePart_iff (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) (outcome : Outcome Result) :
    outcome ∈ cfg.denotePart evalOp input ↔ ∃ fuel, cfg.run evalOp fuel input = some outcome :=
  Proofs.MLIR.CF.SwitchAssert.mem_denotePart_iff cfg evalOp input outcome

/-- A finite return preserves its exact tuple as `Part.some (.returned values)`.
A finite abort is the defined value `Part.some .aborted`. -/
theorem Cfg.denotePart_eq_some_iff (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) (outcome : Outcome Result) :
    cfg.denotePart evalOp input = Part.some outcome ↔
      ∃ fuel, cfg.run evalOp fuel input = some outcome :=
  Part.eq_some_iff.trans (cfg.mem_denotePart_iff evalOp input outcome)

/-- Undefinedness is divergence across all finite budgets. -/
theorem Cfg.denotePart_eq_none_iff (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) : cfg.denotePart evalOp input = Part.none ↔ cfg.Diverges evalOp input :=
  Proofs.MLIR.CF.SwitchAssert.denotePart_eq_none_iff cfg evalOp input

end Silmaril.MLIR.CF.SwitchAssert
