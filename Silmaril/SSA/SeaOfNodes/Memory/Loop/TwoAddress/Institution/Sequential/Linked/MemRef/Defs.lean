module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Defs

/-! One ordered CF graph linking two existing MemRef loop emitters. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef

open RVSDG (Tuple)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Edge Terminator)
open Silmaril.MLIR.CF.Ordered (Block Cfg)
open Silmaril.MLIR.MemRef (Buffer)
open Silmaril.MLIR.Pure (Operands)
open Loop.MLIR.MemRef.CF (wordWidth resultTypes)
open TwoAddress.MemRef (Runtime)

abbrev pairTypes : List Width := wordWidth :: resultTypes

inductive Label (cells : Nat) : List Width → Type where
  | first {ins : List Width} : TwoAddress.MemRef.Label cells ins → Label cells ins
  | secondEntry : Label cells resultTypes
  | second {ins : List Width} : TwoAddress.MemRef.Label cells ins → Label cells (wordWidth :: ins)

inductive Body (cells : Nat) (ambient next : List ValueSort) : List Width → List Width → Type where
  | first {ins outs : List Width} :
      TwoAddress.MemRef.Body cells ambient ins outs → Body cells ambient next ins outs
  | second {ins outs : List Width} :
      TwoAddress.MemRef.Body cells next ins outs → Body cells ambient next (wordWidth :: ins) (wordWidth :: outs)

variable {cells : Nat} {ambient next : List ValueSort} {scope : List Width}

/-- The reserved word dominates the second entry and remains a block
argument across every second-stage edge, including feedback. -/
def carryOperands {delta : List Width} : Operands scope delta → Operands (wordWidth :: scope) delta
  | .nil => .nil
  | .cons var rest => .cons (.there var) (carryOperands rest)

def firstEdge (edge : Edge (TwoAddress.MemRef.Label cells) scope) : Edge (Label cells) scope :=
  ⟨.first edge.label, edge.args⟩

def secondEdge (edge : Edge (TwoAddress.MemRef.Label cells) scope) :
    Edge (Label cells) (wordWidth :: scope) :=
  ⟨.second edge.label, .cons .here (carryOperands edge.args)⟩

def firstTerm : Terminator (TwoAddress.MemRef.Label cells) resultTypes scope →
    Terminator (Label cells) pairTypes scope
  | .br edge => .br (firstEdge edge)
  | .condBr test yes no => .condBr test (firstEdge yes) (firstEdge no)
  | .ret values => .br ⟨.secondEntry, values⟩

def secondTerm : Terminator (TwoAddress.MemRef.Label cells) resultTypes scope →
    Terminator (Label cells) pairTypes (wordWidth :: scope)
  | .br edge => .br (secondEdge edge)
  | .condBr test yes no => .condBr (.there test) (secondEdge yes) (secondEdge no)
  | .ret values => .ret (.cons .here (carryOperands values))

def firstBlock (block : Block (TwoAddress.MemRef.Body cells ambient)
    (TwoAddress.MemRef.Label cells) scope resultTypes) :
    Block (Body cells ambient next) (Label cells) scope pairTypes :=
  ⟨.first block.body, firstTerm block.terminator⟩

def secondBlock (block : Block (TwoAddress.MemRef.Body cells next)
    (TwoAddress.MemRef.Label cells) scope resultTypes) :
    Block (Body cells ambient next) (Label cells) (wordWidth :: scope) pairTypes :=
  ⟨.second block.body, secondTerm block.terminator⟩

/-- Both sides use the original body interpreter in the same buffer
monad. The second tuple is selected from immutable captures and the
reserved word, which is carried unchanged by the block. -/
def evalBody (wiring : Boundary.Wiring ambient next) (input : Tuple (Val cells) ambient) :
    {ins outs : List Width} → Body cells ambient next ins outs → Env ins → Runtime cells (Env outs)
  | _, _, .first code, env => TwoAddress.MemRef.evalBody input code env
  | _, _, .second code, .cons word env => do
    let output ← TwoAddress.MemRef.evalBody (wiring.select word input) code env
    pure (.cons word output)

/-- Reuse both component CFGs. The first actual return becomes the
branch to the second actual entry, and only the second exit returns. -/
def lower (cells : Nat) (first : Graph ambient) (second : Graph next) :
    Cfg (Body cells ambient next) (Label cells) [] pairTypes where
  entry := firstBlock (TwoAddress.MemRef.lower cells first).entry
  block
    | .first label => firstBlock ((TwoAddress.MemRef.lower cells first).block label)
    | .secondEntry => secondBlock (TwoAddress.MemRef.lower cells second).entry
    | .second label => secondBlock ((TwoAddress.MemRef.lower cells second).block label)

abbrev Result (cells : Nat) := Word × Word × Buffer cells

def runFuel (first : Graph ambient) (second : Graph next) (wiring : Boundary.Wiring ambient next)
    (input : Tuple (Val cells) ambient) (fuel : Nat) (initial : Buffer cells) : Option (Result cells) := do
  let (returned, final) ← ((lower cells first second).run (evalBody wiring input) fuel .nil).run initial
  returned.map fun values => (values.get .here, values.get (.there .here), final)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef
