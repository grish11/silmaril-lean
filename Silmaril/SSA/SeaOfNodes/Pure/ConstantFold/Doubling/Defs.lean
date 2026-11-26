module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite.Defs

/-! Replace a nonliteral same-source word addition with multiplication by two. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Doubling

open Diamond (Ty ValueSort dataPorts)
open GVN.Elimination (Rewrite)
open SubZero (wordPort)
open RVSDG (Origin)

variable {args : List (Ty Unit)} {past : List (List (Ty Unit))}
variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}

/-- Give the existing literal fold priority, then compare the actual two
operand origins within the same typed prefix. -/
def matchAdd? (known : Literals args past) (lhs rhs : Origin args past wordPort) :
    Option (AddRewrite.Edit args past) :=
  if (binaryLiteral? known .add (.cons lhs (.cons rhs .nil))).isNone && decide (lhs.address = rhs.address) then
    some ⟨.mul, lhs, 2⟩
  else none

def rules : AddRewrite.Rules args (Literals args) where
  record known op operands := (arithmeticRules op).record known operands
  matchAdd? known lhs rhs := (Doubling.matchAdd? known lhs rhs).map AddRewrite.Edit.splice

/-- Rewrite the first addition admitted by the doubling rule. -/
def step? (program : Program SubZero.Opcode inputs out) : Option (Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs) :=
  AddRewrite.scan? rules (fun _ => none) program.dataflow

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Doubling
