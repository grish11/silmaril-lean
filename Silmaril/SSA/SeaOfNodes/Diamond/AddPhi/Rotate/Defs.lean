module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Defs

/-! The literal-right rotated spine in Simple chapter 8's AddNode.phiCon.
One runtime argument is captured by a native straight-line continuation. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate

open Pure.SubZero (model word wordPort)
open RVSDG (Port Tuple)

variable {inputs joined : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

abbrev InputWord (inputs : List (ValueSort Unit)) := Port (dataPorts inputs) wordPort

/-- A native diamond followed by a typed pure program. The continuation
receives the original runtime word, then the selected join values. -/
structure Program (inputs : List (ValueSort Unit)) (sigs : List (List (Ty Unit)))
    (joined : List (ValueSort Unit)) where
  residual : InputWord inputs
  diamond : Arms.Graph Pure.SubZero.Opcode inputs sigs joined
  suffix : Pure.Program Pure.SubZero.Opcode (word :: joined) word

def Program.atSlot (p : Program inputs sigs joined)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) : BitVec 64 :=
  p.suffix.eval model (.cons (entry.get p.residual)
    ((p.diamond.arms slot).eval model entry (p.diamond.shared.eval model entry PUnit.unit)))

def Program.denote (p : Program inputs sigs joined)
    (entry : Tuple (Val model.value) (dataPorts inputs)) : BitVec 64 :=
  p.suffix.eval model (.cons (entry.get p.residual) (p.diamond.denote model entry))

def Program.Returns (p : Program inputs sigs joined) (entry : Tuple (Val model.value) (dataPorts inputs))
    (result : BitVec 64) : Prop :=
  ∃ values, p.diamond.Returns model entry values ∧
    p.suffix.eval model (.cons (entry.get p.residual) values) = result

/-- The original two bindings are ordered as `inner = x + phi`, then
`result = inner + k`. The outer left wire is the actual inner result. -/
def spine : Pure.Program Pure.SubZero.Opcode [word, word, word] word where
  dataflow := .cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.arg (.tail (.tail .head))) .nil)) .nil)
  result := .output (1 : Fin 2) .head

/-- The replacement's only post-join binding is `x + foldedPhi`. -/
def residualAdd : Pure.Program Pure.SubZero.Opcode [word, word] word where
  dataflow := .cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil)) .nil
  result := .output (0 : Fin 1) .head

/-- Nominate the exact source shape using the original Region. Each row
passes its Φ operand and the same shared outer RHS to the suffix. -/
def original (g : WordGraph inputs sigs) (x : InputWord inputs) (k : WordWire inputs sigs) :
    Program inputs sigs [word, word] where
  residual := x
  diamond := {
    shared := g.dataflow
    predicate := g.predicate
    merge := g.phi.merge
    arms := fun slot => {
      sigs := []
      dataflow := .nil
      outputs := .cons (g.phi.operand slot) (.cons k .nil) } }
  suffix := spine

/-- Link the folded Φ to the residual add and capture the original input. -/
def emit (x : InputWord inputs) (folded : Result inputs sigs) : Program inputs sigs [word] :=
  ⟨x, folded, residualAdd⟩

/-- The fixed orientation and the runtime argument come from the
nomination. The direct literal checker supplies the occurrence folds
and refuses a constant Φ column or an earlier right-zero case. -/
def rewrite? (g : WordGraph inputs sigs) (x : InputWord inputs) (k : WordWire inputs sigs) :
    Option (Program inputs sigs [word]) :=
  (AddPhi.rewrite? g k).map (emit x)

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate
