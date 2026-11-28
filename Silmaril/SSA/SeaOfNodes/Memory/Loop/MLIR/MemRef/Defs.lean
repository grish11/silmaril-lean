module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs

/-! One emitted MemRef activation with the ordered block's typed feedback selector. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef

open RVSDG (Dialect Origin Tuple)
open RVSDG.MLIR.Graph.Feedback (Operands StraightBlock)
open RVSDG.NestedTheta.ExplicitRuntime.Splice (weaken)
open RVSDG.OrderedRuntime.Structured (Values newestIndex newestPort)
open Silmaril.MLIR.MemRef (Buffer Ty Value ValueType wordPorts)
open SeaOfNodes.Memory.MLIR.MemRef (encodeInput entryPorts scalarPort)

variable {args : List ValueSort} {cells : Nat}

abbrev testPorts (cells : Nat) : List (Ty cells) := [.control 2]
abbrev activationPorts (cells : Nat) : List (Ty cells) := .control 2 :: wordPorts cells

/-- The comparison's i1 result uses the two-way control carrier. -/
inductive Op (cells : Nat) : Dialect (ValueType cells) PUnit where
  | memory {ins outs : List (Ty cells)} : Silmaril.MLIR.MemRef.Op cells ins outs → Op cells ins outs
  | cmpiNe : Op cells [.value .i64, .value .i64] (testPorts cells)

def Op.name {ins outs : List (Ty cells)} : Op cells ins outs → String
  | .memory op => op.name
  | .cmpiNe => "arith.cmpi ne"

/-- Feedback selector zero exits and selector one restarts. -/
def tailSelector (word stop : Word) : ULift (Fin 2) :=
  if word = stop then ⟨0⟩ else ⟨1⟩

def runOp (cells : Nat) : {ins outs : List (Ty cells)} → Op cells ins outs →
    Tuple (Values (Value cells)) ins → StateM (Buffer cells) (Tuple (Values (Value cells)) outs)
  | _, _, .memory op, input => (Silmaril.MLIR.MemRef.model cells).effect op input
  | _, _, .cmpiNe, .cons word (.cons stop .nil) =>
    pure (.cons (tailSelector word stop) .nil)

def stopWire (graph : Graph args) (past : List (List (Ty cells))) :
    Origin [] (entryPorts cells args :: past) (.value .i64) :=
  .output 0 (.tail (scalarPort graph.stop))

/-- Append the actual tail comparison and yield its selector and the word
from the ordered body's return. The buffer stays in the monadic state. -/
def tailCode (graph : Graph args) {past : List (List (Ty cells))}
    (word : Operands (entryPorts cells args :: past) (wordPorts cells)) :
    StraightBlock (Op cells) (entryPorts cells args :: past) (activationPorts cells) :=
  let scope := entryPorts cells args :: past
  let value := word.get .head
  let test := Origin.output (newestIndex (testPorts cells) scope) (newestPort .head scope)
  ⟨.prim .cmpiNe (.cons value (.cons (stopWire graph past) .nil))
    (.yield (.cons test (.cons (weaken (testPorts cells) value) .nil))), trivial⟩

abbrev Activation (cells : Nat) (args : List ValueSort) :=
  StraightBlock (Op cells) [entryPorts cells args] (activationPorts cells)

def lowerActivation (cells : Nat) (graph : Graph args) : Activation cells args :=
  let body := SeaOfNodes.Memory.MLIR.MemRef.lower cells graph.body
  body.val.mapYield Op.memory (tailCode graph) body.property

/-- Execute a typed activation already emitted by the body compiler. -/
def evalActivation (block : Activation cells args) (input : Tuple (Val cells) args) :
    StateM (Buffer cells) (Tuple (Values (Value cells)) (activationPorts cells)) :=
  block.val.runStraightLine (runOp cells) block.property (encodeInput input, PUnit.unit)

def runActivation (graph : Graph args) (input : Tuple (Val cells) args) :
    StateM (Buffer cells) (Tuple (Values (Value cells)) (activationPorts cells)) :=
  evalActivation (lowerActivation cells graph) input

/-- Decode one emitted activation's tail result. Both outcomes retain the
entire updated buffer, which is the starting state for a restart. -/
def observeActivation (graph : Graph args) (input : Tuple (Val cells) args) (initial : Buffer cells) :
    (Word × Buffer cells) ⊕ Buffer cells :=
  let (.cons test result, final) := runActivation graph input initial
  if test.down = 0 then .inl (result.get .head, final) else .inr final

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef
