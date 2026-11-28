module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.Defs

/-! The non-Φ left-spine permutation from Simple chapter 8. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine

open Diamond (Ty ValueSort dataPorts)
open GVN (newest weaken)
open GVN.Elimination (Rewrite)
open RightSpine (Addends Prefix WordWire)
open SubZero (word wordPort)
open RVSDG (Address)

variable {args : List (Ty Unit)} {past : List (List (Ty Unit))}
variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}

/-- Optional signed Java source node IDs keyed by addresses of the original table. -/
structure SourceIds where
  lookup : Address → Option Int32

def SourceIds.atWire (ids : SourceIds) (wire : WordWire args past) : Option Int32 :=
  ids.lookup wire.address

/-- Non-Φ `spine_cmp`. A pair of nonliteral wires needs two source IDs. -/
def compare? (ids : SourceIds) (known : Literals args past) (hi lo : WordWire args past) : Option Bool :=
  if (known lo).isSome then some false
  else if (known hi).isSome then some true
  else do
    let hiId ← ids.atWire hi
    let loId ← ids.atWire lo
    return decide (hiId < loId)

/-- Build the private `x + z` and the replacement `(x + z) + y`
from the original left add's ordered `x, y` and the outer right wire. -/
def permute (leftAdd : Addends args past) (right : WordWire args past) : AddRewrite.Splice args past :=
  ⟨⟨[word, word], .add, .cons leftAdd.left (.cons right .nil)⟩,
    ⟨[word, word], .add, .cons (newest .head) (.cons (weaken [wordPort] leftAdd.right) .nil)⟩⟩

/-- Select the later left-spine case after the literal, same-source, and
right-add cases. Literal right wires also belong to the earlier add-chain
case when the inner right wire is literal. -/
def matchAdd? (ids : SourceIds) (known : Prefix args past) (lhs rhs : WordWire args past) :
    Option (AddRewrite.Splice args past) :=
  if (known.literals lhs).isNone && (known.literals rhs).isNone &&
      decide (lhs.address ≠ rhs.address) && (known.addends rhs).isNone then
    (known.addends lhs).bind fun left =>
      if compare? ids known.literals left.right rhs = some true then some (permute left rhs) else none
  else none

def rules (ids : SourceIds) : AddRewrite.Rules args (Prefix args) where
  record := Prefix.record
  matchAdd? := LeftSpine.matchAdd? ids

/-- Permute the first left spine admitted by the supplied source order. -/
def step? (ids : SourceIds) (program : Program SubZero.Opcode inputs out) :
    Option (Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs) :=
  AddRewrite.scan? (rules ids) Prefix.empty program.dataflow

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine
