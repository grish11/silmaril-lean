module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Defs

/-! Rewrite one word addition using one fresh private producer. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite

open Diamond (Dataflow Ty Val ValueSort dataPorts)
open GVN (newest weaken)
open GVN.Elimination (Rewrite Routing routeSuffix)
open SubZero (model word wordPort)
open RVSDG (Locals Origin Tuple Wires)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {inputs ins : List (ValueSort Unit)} {out : ValueSort Unit}
variable {Facts : List (List (Ty Unit)) → Type}

/-- A binary replacement whose left wire is already in scope. -/
structure Edit (args : List (Ty Unit)) (past : List (List (Ty Unit))) where
  opcode : SubZero.BinaryOpcode
  left : Origin args past wordPort
  right : BitVec 64

def Edit.eval (edit : Edit args past) (entry : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) : BitVec 64 :=
  model.run edit.opcode (.cons (Diamond.read model edit.left entry locals) (.cons edit.right .nil))

/-- Wires for the new binary binding after its literal comes into scope. -/
def Edit.operands (edit : Edit args past) : Wires args (past ++ [[wordPort]]) (dataPorts [word, word]) :=
  .cons (weaken [wordPort] edit.left) (.cons (newest .head) .nil)

/-- One word-producing binding with its actual typed inputs. -/
structure Binding (args : List (Ty Unit)) (past : List (List (Ty Unit))) where
  ins : List (ValueSort Unit)
  opcode : SubZero.Opcode ins word
  operands : Wires args past (dataPorts ins)

def Binding.eval (binding : Binding args past) (entry : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) : BitVec 64 :=
  model.run binding.opcode (binding.operands.read entry locals)

/-- The first binding is private to the edit. The second supplies the
original addition's result and may refer to the private binding. -/
structure Splice (args : List (Ty Unit)) (past : List (List (Ty Unit))) where
  privateBinding : Binding args past
  replacement : Binding args (past ++ [[wordPort]])

def Splice.eval (edit : Splice args past) (entry : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) : BitVec 64 :=
  edit.replacement.eval entry (locals.snoc (.cons (edit.privateBinding.eval entry locals) .nil))

def Edit.splice (edit : Edit args past) : Splice args past :=
  ⟨⟨[], .literal edit.right, .nil⟩, ⟨[word, word], edit.opcode, edit.operands⟩⟩

/-- Extend analyzed prefix facts or propose an edit for the actual ordered add operands. -/
structure Rules (args : List (Ty Unit)) (Facts : List (List (Ty Unit)) → Type) where
  record : ∀ {past ins out}, Facts past → SubZero.Opcode ins out → Wires args past (dataPorts ins) →
    Facts (past ++ [[.value out]])
  matchAdd? : ∀ {past}, Facts past → Origin args past wordPort → Origin args past wordPort →
    Option (Splice args past)

/-- The prefix invariant and the local value equation required of a rule. -/
structure Sound (rules : Rules args Facts) (entry : Tuple (Val model.value) args) where
  Agrees : ∀ {past}, Facts past → Locals (Val model.value) past → Prop
  record : ∀ {past ins out} {facts : Facts past} {locals} (op : SubZero.Opcode ins out)
    (operands : Wires args past (dataPorts ins)), Agrees facts locals →
    Agrees (rules.record facts op operands) (locals.snoc (.cons (model.run op (operands.read entry locals)) .nil))
  replaceAdd : ∀ {past} {facts : Facts past} {locals} {lhs rhs : Origin args past wordPort} {edit},
    Agrees facts locals → rules.matchAdd? facts lhs rhs = some edit →
    model.run .add (.cons (Diamond.read model lhs entry locals) (.cons (Diamond.read model rhs entry locals) .nil)) =
      edit.eval entry locals

/-- Insert the private binding, attach the original result to the replacement,
and route every original wire through the extended scope. -/
def insertSplice (edit : Splice args past) (rest : Dataflow SubZero.Opcode args (past ++ [[wordPort]]) sigs) :
    Rewrite SubZero.Opcode args past ([wordPort] :: sigs) :=
  let lift : Routing args past (past ++ [[wordPort]]) := fun wire => weaken [wordPort] wire
  let suffix := routeSuffix rest (lift.push [wordPort])
  ⟨_, .cons edit.privateBinding.opcode edit.privateBinding.operands
    (.cons edit.replacement.opcode edit.replacement.operands suffix.1), suffix.2⟩

/-- Insert a fresh right literal for a binary replacement. -/
def insert (edit : Edit args past) (rest : Dataflow SubZero.Opcode args (past ++ [[wordPort]]) sigs) :
    Rewrite SubZero.Opcode args past ([wordPort] :: sigs) :=
  insertSplice edit.splice rest

def atHead? (rules : Rules args Facts) (facts : Facts past) :
    (op : SubZero.Opcode ins out) → Wires args past (dataPorts ins) →
    Dataflow SubZero.Opcode args (past ++ [[.value out]]) sigs →
    Option (Rewrite SubZero.Opcode args past ([.value out] :: sigs))
  | .add, .cons lhs (.cons rhs .nil), rest => (rules.matchAdd? facts lhs rhs).map (insertSplice · rest)
  | .literal _, _, _ | .sub, _, _ | .mul, _, _ => none

/-- Rewrite the first accepted addition in dependency order. -/
def scan? (rules : Rules args Facts) : {past sigs : List (List (Ty Unit))} →
    Facts past → Dataflow SubZero.Opcode args past sigs → Option (Rewrite SubZero.Opcode args past sigs)
  | _, _, _, .nil => none
  | _, _, facts, .cons op operands rest =>
    match atHead? rules facts op operands rest with
    | some rewrite => some rewrite
    | none => (scan? rules (rules.record facts op operands) rest).map fun rewrite =>
      ⟨_, .cons op operands rewrite.flow, rewrite.route⟩

/-- Read the original return through the rewrite's typed map. -/
def rewrittenProgram (program : Program SubZero.Opcode inputs out)
    (rewrite : Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs) : Program SubZero.Opcode inputs out :=
  { dataflow := rewrite.flow, result := rewrite.route program.result }

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite
