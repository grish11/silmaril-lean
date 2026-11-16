module

public import Silmaril.Wasm.Logic.Hoare.Wasm
public import Silmaril.Wasm.Logic.Core.Thms

@[expose] public section
namespace Silmaril.Logic.Hoare.Wasm
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.Core (Post)

/-- Actual native instructions, with full-width wrapping i32 operands. -/
def addBlock (x y : BitVec 32) : List Instr :=
  [.intConst .i32 x, .intConst .i32 y, .intBinOp .i32 .add]

/-- Preserve the complete store, frame and arbitrary older operand stack. -/
def addPost {H : Type} (s : Store H) (f : Frame) (vs : List Val) (x y : BitVec 32) : Post H :=
  fun s' f' o => s' = s ∧ f' = f ∧ o = .normal (vs ++ [.i32 (x + y)])

end Silmaril.Logic.Hoare.Wasm
