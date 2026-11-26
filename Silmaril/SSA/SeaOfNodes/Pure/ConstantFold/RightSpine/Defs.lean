module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite.Defs

/-! Rotate an add on the right spine after the source's earlier swap case. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine

open Diamond (Ty Val ValueSort dataPorts)
open GVN (newest weaken)
open GVN.Elimination (Rewrite splitOrigin)
open SubZero (model word wordPort)
open RVSDG (Locals Origin Tuple Wires)

variable {args : List (Ty Unit)} {past : List (List (Ty Unit))}
variable {ins inputs : List (ValueSort Unit)} {out : ValueSort Unit}

abbrev WordWire (args : List (Ty Unit)) (past : List (List (Ty Unit))) :=
  Origin args past wordPort

/-- The actual ordered operands of an earlier addition. -/
structure Addends (args : List (Ty Unit)) (past : List (List (Ty Unit))) where
  left : WordWire args past
  right : WordWire args past

def Addends.weaken (pair : Addends args past) : Addends args (past ++ [[wordPort]]) :=
  ⟨GVN.weaken [wordPort] pair.left, GVN.weaken [wordPort] pair.right⟩

def Addends.eval (pair : Addends args past) (entry : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) : BitVec 64 :=
  BitVec.add (Diamond.read model pair.left entry locals) (Diamond.read model pair.right entry locals)

/-- A recorded pair denotes the value at its typed add result. -/
def Addends.Agree (addends : WordWire args past → Option (Addends args past))
    (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past) : Prop :=
  ∀ wire pair, addends wire = some pair → Diamond.read model wire entry locals = pair.eval entry locals

structure Prefix (args : List (Ty Unit)) (past : List (List (Ty Unit))) where
  literals : Literals args past
  addends : WordWire args past → Option (Addends args past)

def Prefix.empty : Prefix args [] := ⟨fun _ => none, fun _ => none⟩

/-- Both literal and ordered-add facts agree with the same prefix store. -/
def Prefix.Agrees (known : Prefix args past) (entry : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) : Prop :=
  Scan.Literals.Agrees known.literals entry locals ∧ Addends.Agree known.addends entry locals

def Prefix.extendAddends (known : Prefix args past) (fresh : Option (Addends args past))
    (wire : WordWire args (past ++ [[wordPort]])) : Option (Addends args (past ++ [[wordPort]])) :=
  let found := match splitOrigin [wordPort] wire with
    | .inl earlier => known.addends earlier
    | .inr .head => fresh
    | .inr (.tail port) => nomatch port
  found.map Addends.weaken

def Prefix.record (known : Prefix args past) (op : SubZero.Opcode ins out)
    (operands : Wires args past (dataPorts ins)) : Prefix args (past ++ [[.value out]]) where
  literals := (arithmeticRules op).record known.literals operands
  addends := match op, operands with
    | .add, .cons lhs (.cons rhs .nil) => known.extendAddends (some ⟨lhs, rhs⟩)
    | .literal _, _ | .sub, _ | .mul, _ => known.extendAddends none

/-- Build the private `x + y` and the replacement `(x + y) + z`.
Here `x` is the original left input and the right add supplies `y, z`. -/
def rotate (x : WordWire args past) (rightAdd : Addends args past) : AddRewrite.Splice args past :=
  ⟨⟨[word, word], .add, .cons x (.cons rightAdd.left .nil)⟩,
    ⟨[word, word], .add, .cons (newest .head) (.cons (weaken [wordPort] rightAdd.right) .nil)⟩⟩

/-- The rotation is reached with two distinct additions in the native
nonconstant profile. A non-add left input belongs to the earlier swap case. -/
def matchAdd? (known : Prefix args past) (lhs rhs : WordWire args past) : Option (AddRewrite.Splice args past) :=
  if (known.literals lhs).isNone && (known.literals rhs).isNone && decide (lhs.address ≠ rhs.address) then
    (known.addends lhs).bind fun _ => (known.addends rhs).map (rotate lhs)
  else none

def rules : AddRewrite.Rules args (Prefix args) where
  record := Prefix.record
  matchAdd? := RightSpine.matchAdd?

/-- Apply one right-spine rotation in dependency order. -/
def step? (program : Program SubZero.Opcode inputs out) : Option (Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs) :=
  AddRewrite.scan? rules Prefix.empty program.dataflow

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine
