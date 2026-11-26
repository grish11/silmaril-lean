module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite.Defs

/-! Combine the right literals of two adjacent additions on an add spine. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain

open Diamond (Dataflow Ty Val ValueSort dataPorts)
open GVN (weaken)
open GVN.Elimination (Rewrite splitOrigin)
open SubZero (model wordPort)
open RVSDG (Locals Origin Tuple Wires)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {ins : List (ValueSort Unit)} {out : ValueSort Unit}

abbrev WordWire (args : List (Ty Unit)) (past : List (List (Ty Unit))) :=
  Origin args past wordPort

/-- A wire plus a literal offset in the same typed prefix. -/
structure Offset (args : List (Ty Unit)) (past : List (List (Ty Unit))) where
  base : WordWire args past
  value : BitVec 64

structure Prefix (args : List (Ty Unit)) (past : List (List (Ty Unit))) where
  literals : Literals args past
  additions : WordWire args past → Option (Offset args past)

def Prefix.empty : Prefix args [] := ⟨fun _ => none, fun _ => none⟩

/-- Explicit literal and constant-offset facts agree with the original prefix. -/
def Prefix.Agrees (known : Prefix args past) (entry : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) : Prop :=
  Scan.Literals.Agrees known.literals entry locals ∧
  ∀ (wire : WordWire args past) {offset}, known.additions wire = some offset →
    Diamond.read model wire entry locals =
      BitVec.add (Diamond.read model offset.base entry locals) offset.value

/-- An add with a literal right operand and a left operand without a literal
fact. Leave two-literal adds and the right identity to their existing rules. -/
def Prefix.rightLiteral? (known : Prefix args past) (lhs rhs : WordWire args past) :
    Option (Offset args past) :=
  match known.literals lhs, known.literals rhs with
  | none, some value =>
    let offset : BitVec 64 := value
    if offset = 0 then none else some ⟨lhs, offset⟩
  | _, _ => none

def Prefix.push (known : Prefix args past) (literal : Option (BitVec 64))
    (addition : Option (Offset args past)) : Prefix args (past ++ [[wordPort]]) where
  literals := Scan.Literals.push (out := SubZero.word) known.literals literal
  additions wire :=
    let prior := match splitOrigin [wordPort] wire with
      | .inl earlier => known.additions earlier
      | .inr .head => addition
      | .inr (.tail port) => nomatch port
    prior.map fun offset => ⟨weaken [wordPort] offset.base, offset.value⟩

def Prefix.record (known : Prefix args past) :
    (op : SubZero.Opcode ins out) → Wires args past (dataPorts ins) → Prefix args (past ++ [[.value out]])
  | .literal value, _ => known.push (some value) none
  | .add, .cons lhs (.cons rhs .nil) => known.push none (known.rightLiteral? lhs rhs)
  | .sub, _ | .mul, _ => known.push none none

def Prefix.combine? (known : Prefix args past) (lhs rhs : WordWire args past) :
    Option (Offset args past) := do
  let outer ← known.rightLiteral? lhs rhs
  let inner ← known.additions outer.base
  return ⟨inner.base, inner.value + outer.value⟩

def rules : AddRewrite.Rules args (Prefix args) where
  record := Prefix.record
  matchAdd? known lhs rhs := (known.combine? lhs rhs).map fun offset =>
    (AddRewrite.Edit.mk .add offset.base offset.value).splice

/-- Insert the combined literal before the replacement add. -/
abbrev insertCombined (offset : Offset args past) (rest : Dataflow SubZero.Opcode args (past ++ [[wordPort]]) sigs) :
    Rewrite SubZero.Opcode args past ([wordPort] :: sigs) :=
  AddRewrite.insert ⟨.add, offset.base, offset.value⟩ rest

abbrev atHead? (known : Prefix args past) (op : SubZero.Opcode ins out) (operands : Wires args past (dataPorts ins))
    (rest : Dataflow SubZero.Opcode args (past ++ [[.value out]]) sigs) :
    Option (Rewrite SubZero.Opcode args past ([.value out] :: sigs)) :=
  AddRewrite.atHead? rules known op operands rest

/-- Scan in dependency order and rewrite the first admitted outer addition. -/
abbrev stepDataflow? (known : Prefix args past) (flow : Dataflow SubZero.Opcode args past sigs) :
    Option (Rewrite SubZero.Opcode args past sigs) :=
  AddRewrite.scan? rules known flow

variable {inputs : List (ValueSort Unit)}

/-- Try a single constant-chain rewrite. The result carries the typed map
from every original producer or argument wire to the rewritten table. -/
def step? (program : Program SubZero.Opcode inputs out) : Option (Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs) :=
  stepDataflow? Prefix.empty program.dataflow

/-- Read the original return through the rewrite's typed map. -/
abbrev rewrittenProgram (program : Program SubZero.Opcode inputs out)
    (rewrite : Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs) : Program SubZero.Opcode inputs out :=
  AddRewrite.rewrittenProgram program rewrite

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain
