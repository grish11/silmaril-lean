module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Defs

/-! Materialize the equal folded operands of the rotated two-Φ case.
The Region exports an empty tuple and the residual program reads the capture. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse

open Pure.SubZero (word)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

inductive Refusal where
  | nonliteralOperand
  | constantOriginalColumn
  | differentSums
  deriving DecidableEq, Repr

/-- The residual add reads a single literal binding and the original argument. -/
def addConstant (value : BitVec 64) : Pure.Program Pure.SubZero.Opcode [word] word where
  dataflow := .cons (.literal value) .nil
    (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil)) .nil)
  result := .output (1 : Fin 2) .head

/-- The immediate right-zero branch returns the capture without a binding. -/
def returnCapture : Pure.Program Pure.SubZero.Opcode [word] word where
  dataflow := .nil
  result := .arg .head

def suffix (value : BitVec 64) : Pure.Program Pure.SubZero.Opcode [word] word :=
  if value = 0 then returnCapture else addConstant value

/-- Retain the original control and drop both value columns from its join. -/
def emit (g : AddPhi.Pair.Source inputs sigs) (x : InputWord inputs) (value : BitVec 64) :
    Program inputs sigs [] where
  residual := x
  diamond := {
    shared := g.shared
    predicate := g.predicate
    merge := g.merge
    arms := fun _ => { sigs := [], dataflow := .nil, outputs := .nil } }
  suffix := suffix value

/-- The original columns must still be Φs when the rotated rule is
selected. Equal new sums materialize one word before the residual add. -/
def rewrite (g : AddPhi.Pair.Source inputs sigs) (x : InputWord inputs) :
    Except Refusal (Program inputs sigs []) :=
  match AddPhi.Pair.literalRows? g with
  | none => .error .nonliteralOperand
  | some (first, second) =>
    if AddPhi.Pair.nonconstantColumns first second then
      let value := AddPhi.Pair.add first
      if value = AddPhi.Pair.add second then .ok (emit g x value) else .error .differentSums
    else .error .constantOriginalColumn

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse
