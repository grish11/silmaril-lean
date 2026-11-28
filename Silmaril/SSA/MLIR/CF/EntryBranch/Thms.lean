module

public import Silmaril.SSA.MLIR.CF.EntryBranch.Defs
import Silmaril.Proofs.SSA.MLIR.CF.EntryBranch.Correctness

public section

namespace Silmaril.MLIR.CF.EntryBranch

open Arith (Width Env)
open Silmaril.MLIR.Pure (OpSignature Eval)

variable {Op : OpSignature} {Arms : Bool → List Width → Type} {Input Result : List Width}

/-- Spend one block on the guard, then execute the chosen CFG at its own fuel
with precisely the same external input. -/
theorem run_entry (guard : Block Op (Label Arms) Input Result)
    (arms : ∀ side, Cfg Op (Arms side) Input Result) (evalOp : Eval Op)
    (input : Env Input) (side : Bool)
    (selected : guard.eval evalOp (fun term vals => Terminator.eval vals term) input = .inl ⟨.entry side, .nil⟩)
    (fuel : Nat) :
    (link guard arms).run evalOp (fuel + 1) input = (arms side).run evalOp fuel input :=
  Proofs.run_entry guard arms evalOp input side selected fuel

end Silmaril.MLIR.CF.EntryBranch
