module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.Defs

/-! Source-ordered entry point for the nominated rotated two-Φ add. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch

open Pure.ConstantFold (Literals)
open Pure.SubZero (model word wordPort)
open RVSDG (Port Tuple extend)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

inductive Refusal where
  | constantColumnPriority
  | nonliteralOperand
  deriving DecidableEq, Repr

/-- Each success carries the actual native program for that source outcome. -/
inductive Result (inputs : List (ValueSort Unit)) (sigs : List (List (Ty Unit))) where
  | residualPhi (program : Program inputs sigs [word])
  | constantAdd (program : Program inputs sigs [])
  | captureOnly (program : Program inputs sigs [])

def Result.denote (result : Result inputs sigs) (entry : Tuple (Val model.value) (dataPorts inputs)) :
    BitVec 64 :=
  match result with
  | .residualPhi p => p.denote entry
  | .constantAdd p | .captureOnly p => p.denote entry

def Result.Returns (result : Result inputs sigs) (entry : Tuple (Val model.value) (dataPorts inputs))
    (value : BitVec 64) : Prop :=
  match result with
  | .residualPhi p => p.Returns entry value
  | .constantAdd p | .captureOnly p => p.Returns entry value

/-- The two original Φs in operand order. -/
inductive Column where
  | left
  | right
  deriving DecidableEq, Repr

def Column.port : Column → Port (dataPorts [word, word]) wordPort
  | .left => .head
  | .right => .tail .head

def Column.other : Column → Column
  | .left => .right
  | .right => .left

/-- Typed literal facts for individual operands of this predecessor. -/
def armWords {args : List (Ty Unit)} {past : List (List (Ty Unit))}
    (known : Literals args past) (arm : Arms.Arm Pure.SubZero.Opcode args past [word, word]) :
    Column → Option (BitVec 64) :=
  let facts : Literals args (extend past arm.sigs) := scanLiterals known arm.dataflow
  fun column => facts (arm.outputs.get column.port)

def equalLiterals? (first second : Option (BitVec 64)) : Option (BitVec 64) := do
  let left ← first
  let right ← second
  if left = right then some left else none

/-- Find equal word literals in each column, independently of the other
column's operands. Both lookups use the actual predecessor occurrences. -/
def constantColumns (g : AddPhi.Pair.Source inputs sigs) : Column → Option (BitVec 64) :=
  let known : Literals (dataPorts inputs) (extend [] sigs) := scanLiterals (fun _ => none) g.shared
  let first := armWords known (g.arms .first)
  let second := armWords known (g.arms .second)
  fun column => equalLiterals? (first column) (second column)

/-- Check priority even when a nonliteral prevented the full row lookup. -/
def hasConstantColumn (g : AddPhi.Pair.Source inputs sigs) : Bool :=
  let columns := constantColumns g
  (columns .left).isSome || (columns .right).isSome

/-- Classify the materialization and the immediate right-zero follow-up. -/
def emit (g : AddPhi.Pair.Source inputs sigs) (x : InputWord inputs)
    (first second : AddPhi.Pair.Operands) : Result inputs sigs :=
  let value := AddPhi.Pair.add first
  if value = AddPhi.Pair.add second then
    if value = 0 then .captureOnly (Collapse.emit g x value)
    else .constantAdd (Collapse.emit g x value)
  else .residualPhi (Rotate.emit x (AddPhi.Pair.emit g first second))

/-- Original column materialization takes precedence over the rotated
rule. The successful path shares one lookup of the ordered literal rows. -/
def rewrite (g : AddPhi.Pair.Source inputs sigs) (x : InputWord inputs) :
    Except Refusal (Result inputs sigs) :=
  match AddPhi.Pair.literalRows? g with
  | none =>
    if hasConstantColumn g then .error .constantColumnPriority else .error .nonliteralOperand
  | some (first, second) =>
    if AddPhi.Pair.nonconstantColumns first second then .ok (emit g x first second)
    else .error .constantColumnPriority

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch
