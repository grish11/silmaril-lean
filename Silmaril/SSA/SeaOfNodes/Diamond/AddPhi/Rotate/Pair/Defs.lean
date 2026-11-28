module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Defs

/-! Rotate `((x + Φ(a,b)) + Φ(c,d))` through one completed Region. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair

open Pure.SubZero (word)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

/-- The two columns must still be Φs at the original add. Distinct sums
keep the new Φ through its immediate constant-materialization check. -/
def eligible (first second : AddPhi.Pair.Operands) : Bool :=
  AddPhi.Pair.nonconstantColumns first second &&
    decide (AddPhi.Pair.add first ≠ AddPhi.Pair.add second)

/-- The join supplies the inner right and outer right operands in order.
The fixed suffix has the inner add at the outer left operand. -/
def original (g : AddPhi.Pair.Source inputs sigs) (x : InputWord inputs) :
    Program inputs sigs [word, word] :=
  ⟨x, g, spine⟩

/-- The doubling guard at the outer add compares the inner Add with the
right Φ. Both Φ operands may refer to the same node. -/
def rewrite? (g : AddPhi.Pair.Source inputs sigs) (x : InputWord inputs) :
    Option (Program inputs sigs [word]) :=
  (AddPhi.Pair.rewriteWith? eligible g).map (Rotate.emit x)

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair
