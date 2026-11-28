module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Defs

/-! Compare entry add operands with recursively numbered incoming Phi wires. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers

open Pure.SubZero (word)
open Pure.RightIdentityPass (wordProducers)
open GVN.WordNumber (Key entryKeys numbering)
open RVSDG (Locals extend)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

/-- The common prefix's word numbers are available in both arms. -/
abbrev SharedKeys (inputs : List (ValueSort Unit)) (sigs : List (List (Ty Unit))) :=
  Locals (Val (numbering (dataPorts inputs)).value) (extend [] sigs)

def sharedKeys (p : Program inputs sigs [word]) : SharedKeys inputs sigs :=
  p.diamond.shared.eval (numbering (dataPorts inputs)) (entryKeys inputs) PUnit.unit

/-- Read an operand of the entry representative at the shared cut. -/
def operandKey (shared : SharedKeys inputs sigs) (wire : SharedWord inputs sigs) :
    Key (dataPorts inputs) :=
  read (numbering (dataPorts inputs)) wire (entryKeys inputs) shared

/-- Number the actual Phi operand at its own predecessor cut, extending
the already numbered entry through just that arm's typed producer table. -/
def phiKey (p : Program inputs sigs [word]) (shared : SharedKeys inputs sigs) (slot : Slot) :
    Key (dataPorts inputs) :=
  let arm := p.diamond.arms slot
  let entry := entryKeys inputs
  let m := numbering (dataPorts inputs)
  read m (arm.outputs.get .head) entry (arm.dataflow.eval m entry shared)

/-- The typed key must describe an ordered add of the capture and a word
with the same structural number as each occurrence's actual Phi operand. -/
def check (p : Program inputs sigs [word]) : EntryAdd p → Bool :=
  let shared := sharedKeys p
  let first := phiKey p shared .first
  let second := phiKey p shared .second
  fun rep => match addOperands? rep.key with
    | none => false
    | some ⟨(lhs, rhs), _⟩ =>
      let right := operandKey shared rhs
      (operandKey shared lhs).matches (.argument p.residual) &&
        right.matches first && right.matches second

/-- Select the first admitted shared word producer in definition order. -/
def findRepresentative? (p : Program inputs sigs [word]) : Option (EntryAdd p) :=
  (wordProducers p.diamond.shared).find? (check p)

/-- Check the actual suffix shape, discover a shared add, and use the
existing typed emitter to forward it to the join. -/
def discoverAndRewrite? (p : Program inputs sigs [word]) : Option (Program inputs sigs [word, word]) := do
  let value ← rightValue? p.suffix
  let rep ← findRepresentative? p
  pure (emit p rep value.val)

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers
