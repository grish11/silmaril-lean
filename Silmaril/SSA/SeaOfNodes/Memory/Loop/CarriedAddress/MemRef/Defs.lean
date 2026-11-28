module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Defs

/-! Typed ordered CF for the occurrence-selected address profile. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef

open RVSDG (Tuple)
open SeaOfNodes.Loop (Incoming)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.MemRef (Buffer)
open Silmaril.MLIR.Pure (i1)
open Loop.MLIR.MemRef (Activation lowerActivation)
open Loop.MLIR.MemRef.CF (resultTypes)
open Silmaril.MLIR.CF.Ordered (Cfg)

abbrev headerTypes : List Width := [i1]

/-- False encodes entry, true encodes feedback. -/
def arrivalEnv (arrival : Incoming) : Env headerTypes :=
  .cons (arrival.select 0 1) .nil

inductive Label : List Width → Type where
  | header : Label headerTypes
  | exit : Label resultTypes

inductive Body (cells : Nat) (args : List ValueSort) : List Width → List Width → Type where
  | entry : Body cells args [] headerTypes
  | activation (code : Activation cells (.address :: args)) :
      Body cells args headerTypes (i1 :: i1 :: resultTypes)
  | exit : Body cells args resultTypes resultTypes

variable {cells : Nat} {args : List ValueSort}

def evalBody (graph : Graph args) (input : Tuple (Val cells) args) :
    {ins outs : List Width} → Body cells args ins outs → Env ins → StateM (Buffer cells) (Env outs)
  | _, _, .entry, _ => pure (arrivalEnv .entry)
  | _, _, .activation code, env => do
    let arrival := if (env.get .here).getLsbD 0 then Incoming.backedge else Incoming.entry
    let values ← Loop.MLIR.MemRef.CF.evalBody (graph.operands input arrival) (.activation code) .nil
    pure (.cons (values.get .here) (.cons 1 (.cons (values.get (.there .here)) .nil)))
  | _, _, .exit, env => pure env

abbrev Program (cells : Nat) (args : List ValueSort) :=
  Cfg (Body cells args) Label [] resultTypes

/-- A real branch passes the entry occurrence to the header, and the
conditional self edge passes the backedge occurrence. Both reuse the
same typed MemRef activation and initialized buffer. -/
def lower (cells : Nat) (graph : Graph args) : Program cells args where
  entry := ⟨.entry, .br ⟨.header, .cons .here .nil⟩⟩
  block
    | .header => ⟨.activation (lowerActivation cells graph.activation),
        .condBr .here ⟨.header, .cons (.there .here) .nil⟩
          ⟨.exit, .cons (.there (.there .here)) .nil⟩⟩
    | .exit => ⟨.exit, .ret (.cons .here .nil)⟩

/-- Observe the returned word and every buffer cell. The raw block fuel
allows one step for entry and exit each, and one plus the allowed
backedges for the header. -/
def runProgram (program : Program cells args) (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (initial : Buffer cells) : Option (Word × Buffer cells) :=
  let (result, final) := program.run (evalBody graph input) (budget + 3) .nil initial
  result.map fun values => (values.get .here, final)

/-- Run the generated program from its root block and initialized buffer. -/
def run (graph : Graph args) (input : Tuple (Val cells) args) (budget : Nat)
    (initial : Buffer cells) : Option (Word × Buffer cells) :=
  runProgram (lower cells graph) graph input budget initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef
