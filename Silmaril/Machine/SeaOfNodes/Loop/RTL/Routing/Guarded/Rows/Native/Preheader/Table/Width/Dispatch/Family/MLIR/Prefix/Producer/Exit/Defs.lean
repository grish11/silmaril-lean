module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Thms

/-! The single signed-guard exit of the checked resized CF/RTL producer profile. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Func)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)

/-- Check the original zero successor and the one-parameter return block.
A different register with the same type or runtime word does not pass. -/
def check (fn : Func Reg) (operand : Reg) : Bool :=
  decide ((fn.block? 1).bind (fun block => block.term.args[1]?) = some (2, [operand]) ∧
    fn.block? 2 = some exitBlock)

variable {old new tests : Nat} {entrySigs sigs : List (List PortTy)}
variable {mapping : InputMap old new} {source : Family.Source old old entrySigs sigs tests}
variable {origins : List (HeaderWord new old sigs)}

/-- Evidence for the taken zero successor at the final header. The RTL
cut preserves the complete memory and changes only the exit parameter
on the branch. CF takes its typed one-word edge before returning it. -/
structure Taken (compiled : Compiled mapping source origins) (input : WordTuple new)
    (mem : Memory) (carried : WordTuple old) (before : Frame Reg) (value : Word) : Prop where
  rtl : ∃ ready, Family.ExitCut (mapCaptures mapping source) compiled.rtl input carried before ready mem value
  checked : check (lowerFunc (mapCaptures mapping source))
    (register (mapCaptures mapping source).primary.result.address) = true
  cfBranch : (compiled.setup.cf.block .header).eval evalOp (fun term env => term.eval env)
    ((wordEnv carried).append (wordEnv input)) = .inl ⟨.exit, .cons value .nil⟩
  cfReturn : (compiled.setup.cf.block .exit).eval evalOp (fun term env => term.eval env)
    ((Silmaril.MLIR.Arith.Env.cons (w := Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF.i64) value .nil).append
      (wordEnv input)) = .inr (.cons value .nil)

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit
