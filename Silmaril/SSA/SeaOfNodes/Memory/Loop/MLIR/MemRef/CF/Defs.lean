module

public import Silmaril.SSA.MLIR.CF.Ordered.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Defs

/-! Emit a CF loop with the ordered MemRef block at its header. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF

open RVSDG (Tuple)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.MemRef (Buffer)
open Silmaril.MLIR.Pure (i1)

abbrev wordWidth : Width := ⟨64, by decide⟩
abbrev resultTypes : List Width := [wordWidth]

inductive Label : List Width → Type where
  | header : Label []
  | exit : Label resultTypes

/-- The activation runs on the invariant typed inputs and the shared buffer.
Only its selector and word become operands of the CF terminator. -/
inductive Body (cells : Nat) (args : List ValueSort) : List Width → List Width → Type where
  | pass {scope : List Width} : Body cells args scope scope
  | activation (code : Activation cells args) : Body cells args [] (i1 :: resultTypes)

variable {cells : Nat} {args : List ValueSort}

def evalBody (input : Tuple (Val cells) args) :
    {ins outs : List Width} → Body cells args ins outs → Env ins → StateM (Buffer cells) (Env outs)
  | _, _, .pass, env => pure env
  | _, _, .activation code, _ => do
    let values ← evalActivation code input
    let selector := (values.get .head).down
    pure (.cons (BitVec.ofBool (selector != 0)) (.cons (values.get (.tail .head)) .nil))

/-- The entry jumps to the header. The conditional edge restarts on one and
otherwise carries the word to the exit. The buffer lives in the monad. -/
def lower (cells : Nat) (graph : Graph args) :
    Silmaril.MLIR.CF.Ordered.Cfg (Body cells args) Label [] resultTypes where
  entry := ⟨.pass, .br ⟨.header, .nil⟩⟩
  block
    | .header => ⟨.activation (lowerActivation cells graph),
        .condBr .here ⟨.header, .nil⟩ ⟨.exit, .cons (.there .here) .nil⟩⟩
    | .exit => ⟨.pass, .ret (.cons .here .nil)⟩

/-- Observe the word and whole buffer of a successful CFG run. An allowance
of `budget` backedges supplies `budget + 3` block steps for entry, headers,
and exit. -/
def run (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (initial : Buffer cells) : Option (Word × Buffer cells) :=
  let (result, final) := (lower cells graph).run (evalBody input) (budget + 3) .nil initial
  result.map fun values => (values.get .here, final)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF
