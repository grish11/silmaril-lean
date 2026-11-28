module

public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Defs
public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Defs

/-! The direct literal-right case of Simple chapter 8's AddNode.phiCon.
The source is one native returned Phi with one additional word-add return use. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi

open Pure.ConstantFold (Literals)
open Pure.SubZero (model word wordPort)
open RVSDG (Origin Tuple extend)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {inputs : List (ValueSort Unit)} {ins : List (ValueSort Unit)} {out : ValueSort Unit}

abbrev WordGraph (inputs : List (ValueSort Unit)) (sigs : List (List (Ty Unit))) :=
  Graph Pure.SubZero.Opcode inputs sigs word

abbrev WordWire (inputs : List (ValueSort Unit)) (sigs : List (List (Ty Unit))) :=
  Origin (dataPorts inputs) (extend [] sigs) wordPort

abbrev Result (inputs : List (ValueSort Unit)) (sigs : List (List (Ty Unit))) :=
  Arms.Graph Pure.SubZero.Opcode inputs sigs [word]

def explicitLiteral : Pure.SubZero.Opcode ins out → Option (Val model.value (.value out))
  | .literal value => some value
  | .add | .sub | .mul => none

/-- Collect explicit literals at their typed addresses in the native table. -/
def scanLiterals : {past sigs : List (List (Ty Unit))} →
    Literals args past → Dataflow Pure.SubZero.Opcode args past sigs → Literals args (extend past sigs)
  | _, _, known, .nil => known
  | _, _, known, .cons op _ rest => scanLiterals (known.push (explicitLiteral op)) rest

abbrev addWords (lhs rhs : BitVec 64) : BitVec 64 :=
  model.run .add (.cons lhs (.cons rhs .nil))

/-- Read the original add operands at a particular Region occurrence. -/
def sourceAt (g : WordGraph inputs sigs) (rhs : WordWire inputs sigs)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) : BitVec 64 :=
  let locals := g.dataflow.eval model entry PUnit.unit
  addWords (read model (g.phi.operand slot) entry locals) (read model rhs entry locals)

/-- The enclosing addition reads the selected native Phi and its shared right wire. -/
def sourceDenote (g : WordGraph inputs sigs) (rhs : WordWire inputs sigs)
    (entry : Tuple (Val model.value) (dataPorts inputs)) : BitVec 64 :=
  addWords (g.denote model entry) (read model rhs entry (g.dataflow.eval model entry PUnit.unit))

/-- The finite source observation composes the native Phi return with the add use. -/
def SourceReturns (g : WordGraph inputs sigs) (rhs : WordWire inputs sigs)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (result : BitVec 64) : Prop :=
  ∃ selected, g.Returns model entry selected ∧
    addWords selected (read model rhs entry (g.dataflow.eval model entry PUnit.unit)) = result

/-- One folded literal in the arm for this occurrence. -/
def literalArm (value : BitVec 64) : Arms.Arm Pure.SubZero.Opcode args past [word] where
  sigs := [[wordPort]]
  dataflow := .cons (.literal value) .nil .nil
  outputs := .cons (GVN.newest .head) .nil

/-- Keep the shared prefix, predicate and Region order. Supply a folded
operand for each old predecessor occurrence. -/
def emit (g : WordGraph inputs sigs) (first second right : BitVec 64) : Result inputs sigs where
  shared := g.dataflow
  predicate := g.predicate
  merge := g.phi.merge
  arms
    | .first => literalArm (addWords first right)
    | .second => literalArm (addWords second right)

/-- Check the actual two Phi wires and the shared RHS for explicit literals.
Unequal arms avoid prior constant materialization. A nonzero RHS avoids the
earlier right-zero rule. The native diamond fixes the complete Region and arity. -/
def rewrite? (g : WordGraph inputs sigs) (rhs : WordWire inputs sigs) : Option (Result inputs sigs) := do
  let known := scanLiterals (fun _ => none) g.dataflow
  let first : BitVec 64 ← known (g.phi.operand .first)
  let second : BitVec 64 ← known (g.phi.operand .second)
  let right : BitVec 64 ← known rhs
  if first = second ∨ right = 0 then none else some (emit g first second right)

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi
