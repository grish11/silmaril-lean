module

public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Mixed.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.MLIR.CF.Mixed.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Mixed

open Diamond (Val ValueSort dataPorts)
open RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.MLIR (Word)
open Silmaril.SSA.SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width Env)

variable {inputs carried : List (ValueSort Width)} {result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable (g : Program inputs carried result entrySigs headerSigs)
variable (input : Tuple (Val Word) (dataPorts inputs))

theorem lower_entry_frame :
    (lower g).entry.eval evalOp (fun term env => term.eval env) (encodeValues input) =
      .inl ⟨.header, encodeValues (g.initial model input)⟩ :=
  Silmaril.Proofs.SSA.SeaOfNodes.Loop.MLIR.CF.Mixed.entry_frame g input

theorem lower_header_frame (old : Tuple (Val Word) (dataPorts carried)) :
    ((lower g).block .header).eval evalOp (fun term env => term.eval env)
      ((encodeValues old).append (encodeValues input)) =
      .inl (match g.step model input old with
        | .inl value => ⟨.exit, .cons value .nil⟩
        | .inr next => ⟨.header, encodeValues next⟩) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Loop.MLIR.CF.Mixed.header_frame g input old

theorem lower_run (budget : Nat) :
    (lower g).run evalOp (budget + 3) (encodeValues input) =
      (g.evalBackedges model budget input).map (fun value => Env.cons value .nil) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Loop.MLIR.CF.Mixed.run_budget g input budget

theorem lower_run_short (fuel : Nat) (short : fuel < 3) :
    (lower g).run evalOp fuel (encodeValues input) = none :=
  Silmaril.Proofs.SSA.SeaOfNodes.Loop.MLIR.CF.Mixed.run_short g input fuel short

end Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Mixed
