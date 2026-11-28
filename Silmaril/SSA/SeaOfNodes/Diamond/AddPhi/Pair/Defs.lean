module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Defs

/-! The direct two-Φ case of Simple chapter 8's AddNode.phiCon.
The two operands are columns of one native join row, with one row per predecessor. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair

open Pure.ConstantFold (Literals)
open Pure.ConstantFold.Scan (literalInputs?)
open Pure.SubZero (model word)
open RVSDG (Tuple extend)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {args : List (Ty Unit)} {past : List (List (Ty Unit))}

abbrev Source (inputs : List (ValueSort Unit)) (sigs : List (List (Ty Unit))) :=
  Arms.Graph Pure.SubZero.Opcode inputs sigs [word, word]

abbrev Operands := Tuple (Val model.value) (dataPorts [word, word])

abbrev add (operands : Operands) : BitVec 64 := model.run .add operands

/-- The original candidate adds both values read at this predecessor occurrence. -/
def sourceAt (g : Source inputs sigs) (entry : Tuple (Val model.value) (dataPorts inputs))
    (slot : Slot) : BitVec 64 :=
  add ((g.arms slot).eval model entry (g.shared.eval model entry PUnit.unit))

def sourceDenote (g : Source inputs sigs) (entry : Tuple (Val model.value) (dataPorts inputs)) : BitVec 64 :=
  add (g.denote model entry)

/-- Compose the native join's finite observation with one nominated return add. -/
def SourceReturns (g : Source inputs sigs) (entry : Tuple (Val model.value) (dataPorts inputs))
    (result : BitVec 64) : Prop :=
  ∃ operands, g.Returns model entry operands ∧ add operands = result

/-- Recover both actual join operands in this arm's typed scope. -/
def armLiterals? (known : Literals args past) (arm : Arms.Arm Pure.SubZero.Opcode args past [word, word]) :
    Option Operands :=
  literalInputs? (scanLiterals known arm.dataflow) arm.outputs

/-- Recover the two typed literal rows in the original Region order. -/
def literalRows? (g : Source inputs sigs) : Option (Operands × Operands) := do
  let known : Literals (dataPorts inputs) (extend [] sigs) := scanLiterals (fun _ => none) g.shared
  let first ← armLiterals? known (g.arms .first)
  let second ← armLiterals? known (g.arms .second)
  return (first, second)

def Operands.left (row : Operands) : BitVec 64 := row.get .head

def Operands.right (row : Operands) : BitVec 64 := row.get (.tail .head)

/-- Each original Φ column has different values across the two occurrences. -/
def nonconstantColumns (first second : Operands) : Bool :=
  decide (first.left ≠ second.left ∧ first.right ≠ second.right)

/-- For the direct add, different values in a row rule out a same-node add. -/
def eligible (first second : Operands) : Bool :=
  nonconstantColumns first second &&
    decide (first.left ≠ first.right ∨ second.left ≠ second.right)

/-- Use the same Region and emit one folded word for each old predecessor. -/
def emit (g : Source inputs sigs) (first second : Operands) : Result inputs sigs where
  shared := g.shared
  predicate := g.predicate
  merge := g.merge
  arms
    | .first => literalArm (add first)
    | .second => literalArm (add second)

/-- Check the four actual literal operands in Region order, then apply
the caller's admission guard to the two rows. -/
def rewriteWith? (admit : Operands → Operands → Bool) (g : Source inputs sigs) :
    Option (Result inputs sigs) := do
  let (first, second) ← literalRows? g
  if admit first second then some (emit g first second) else none

/-- Fold the direct add when its source precedence checks admit both rows. -/
def rewrite? (g : Source inputs sigs) : Option (Result inputs sigs) :=
  rewriteWith? eligible g

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair
