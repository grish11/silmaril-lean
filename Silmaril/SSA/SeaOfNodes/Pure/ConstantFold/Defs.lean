module

public import Silmaril.SSA.SeaOfNodes.Pure.SubZero.Defs

/-! Normalize bindings using their actual typed operand wires.
A replacement occupies the original typed result slot. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold

open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts sortValue)
open GVN.Elimination (splitOrigin)
open SubZero (model word)
open RVSDG (Locals Origin Tuple Wires)

namespace Scan

variable {Op : Signature Unit} {m : Model Op}
variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {ins : List (ValueSort Unit)} {out : ValueSort Unit}

/-- A typed lookup of explicit literal values in the rewritten prefix. -/
abbrev Literals (m : Model Op) (args : List (Ty Unit)) (past : List (List (Ty Unit))) :=
  ∀ {t : Ty Unit}, Origin args past t → Option (Val m.value t)

/-- Each recorded literal agrees with the value at its typed origin. -/
def Literals.Agrees (known : Literals m args past) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) : Prop :=
  ∀ {t : Ty Unit} (wire : Origin args past t) {value}, known wire = some value →
    Diamond.read m wire entry locals = value

/-- Extend the lookup along the existing typed origin split. -/
def Literals.push (known : Literals m args past) (value : Option (Val m.value (.value out))) :
    Literals m args (past ++ [[.value out]]) :=
  fun wire =>
    match splitOrigin (T := Ty Unit) (past := past) [.value out] wire with
    | .inl earlier => known earlier
    | .inr .head => value
    | .inr (.tail port) => nomatch port

/-- Each rule certifies the value of its replacement in the native model. -/
inductive Rule (m : Model Op) : {ins : List (ValueSort Unit)} → {out : ValueSort Unit} →
    Op ins out → Type where
  | literal {out : ValueSort Unit} (op : Op [] out) : Rule m op
  | operation {ins : List (ValueSort Unit)} {out : ValueSort Unit}
      (op : Op ins out) (encode : sortValue m.value out → Op [] out)
      (read_encode : ∀ value, m.run (encode value) .nil = value) : Rule m op
  | sameWord {out : ValueSort Unit} (op : Op [word, word] out) (result : Op [] out)
      (read_same : ∀ value, m.run op (.cons value (.cons value .nil)) = m.run result .nil)
      (fallback : Rule m op) : Rule m op
  | commuteLeftLiteral {out : ValueSort Unit} (op : Op [word, word] out)
      (read_swapped : ∀ lhs rhs, m.run op (.cons rhs (.cons lhs .nil)) = m.run op (.cons lhs (.cons rhs .nil)))
      (fallback : Rule m op) : Rule m op

abbrev Rules (m : Model Op) :=
  ∀ {ins : List (ValueSort Unit)} {out : ValueSort Unit} (op : Op ins out), Rule m op

/-- Read every actual operand wire in signature order, failing on an unknown read. -/
def literalInputs? (known : Literals m args past) {ports : List (Ty Unit)} :
    Wires args past ports → Option (Tuple (Val m.value) ports)
  | .nil => some .nil
  | .cons wire rest =>
    (known wire).bind fun value => (literalInputs? known rest).map (.cons value)

abbrev Rule.binary (op : Op [word, word] out) (encode : sortValue m.value out → Op [] out)
    (read_encode : ∀ value, m.run (encode value) .nil = value) : Rule m op :=
  .operation op encode read_encode

abbrev binaryInputs? (known : Literals m args past)
    (operands : Wires args past (dataPorts [word, word])) :
    Option (Tuple (Val m.value) (dataPorts [word, word])) :=
  literalInputs? known operands

/-- Return a certified literal using the binding's actual typed wires. -/
def Rule.replacement? (known : Literals m args past) :
    {ins : List (ValueSort Unit)} → {out : ValueSort Unit} → {op : Op ins out} →
      Rule m op → Wires args past (dataPorts ins) → Option (Op [] out)
  | _, _, _, .literal original, _ => some original
  | _, _, _, .operation opcode encode _, operands =>
    (literalInputs? known operands).map fun values => encode (m.run opcode values)
  | _, _, _, .sameWord _ result _ fallback, operands =>
    if (operands.get .head).address = (operands.get (.tail .head)).address then some result
    else replacement? known fallback operands
  | _, _, _, .commuteLeftLiteral _ _ fallback, operands => replacement? known fallback operands

/-- Advance the literal facts without rewriting the binding being analyzed. -/
def Rule.record {op : Op ins out} (rule : Rule m op) (known : Literals m args past)
    (operands : Wires args past (dataPorts ins)) : Literals m args (past ++ [[.value out]]) :=
  known.push ((rule.replacement? known operands).map fun literal => m.run literal .nil)

/-- Normalize a surviving binding's operand order. Only a certified
commutative rule can move a known left literal past an unknown right wire. -/
def Rule.orderOperands (known : Literals m args past) :
    {ins : List (ValueSort Unit)} → {out : ValueSort Unit} → {op : Op ins out} →
      Rule m op → Wires args past (dataPorts ins) → Wires args past (dataPorts ins)
  | _, _, _, .literal _, operands => operands
  | _, _, _, .operation _ _ _, operands => operands
  | _, _, _, .sameWord _ _ _ fallback, operands => orderOperands known fallback operands
  | _, _, _, .commuteLeftLiteral _ _ fallback, operands@(.cons lhs (.cons rhs .nil)) =>
    if (known lhs).isSome && (known rhs).isNone then .cons rhs (.cons lhs .nil)
    else orderOperands known fallback operands

/-- Scan once in dependency order, preserving the table's output signatures. -/
def foldDataflow (rules : Rules m) : {past sigs : List (List (Ty Unit))} →
    Literals m args past → Dataflow Op args past sigs → Dataflow Op args past sigs
  | _, _, _, .nil => .nil
  | _, _, known, .cons op operands rest =>
    match (rules op).replacement? known operands with
    | some literal =>
      .cons literal .nil (foldDataflow rules (known.push (some (m.run literal .nil))) rest)
    | none => .cons op ((rules op).orderOperands known operands) (foldDataflow rules (known.push none) rest)

variable {inputs : List (ValueSort Unit)}

/-- Start the scan with no assumptions about the program arguments. -/
def fold (rules : Rules m) (program : Program Op inputs out) : Program Op inputs out :=
  { program with dataflow := foldDataflow rules (fun _ => none) program.dataflow }

end Scan

/-- Word arithmetic rules for the shared forward scan. -/
def arithmeticRules : Scan.Rules model :=
  fun op => match op with
  | .literal value => .literal (SubZero.Opcode.literal value)
  | .add => .binary SubZero.Opcode.add SubZero.Opcode.literal (fun _ => rfl)
  | .sub =>
    .sameWord SubZero.Opcode.sub (SubZero.Opcode.literal 0) (fun value => BitVec.sub_self value)
      (.binary SubZero.Opcode.sub SubZero.Opcode.literal (fun _ => rfl))
  | .mul =>
    .commuteLeftLiteral SubZero.Opcode.mul (fun lhs rhs => BitVec.mul_comm rhs lhs)
      (.binary SubZero.Opcode.mul SubZero.Opcode.literal (fun _ => rfl))

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))} {ins : List (ValueSort Unit)}

abbrev Literals := Scan.Literals model

abbrev Literals.push (known : Literals args past) (value : Option (Val model.value (.value out))) :
    Literals args (past ++ [[.value out]]) :=
  Scan.Literals.push known value

abbrev literal? (known : Literals args past) (op : SubZero.Opcode ins out)
    (operands : Wires args past (dataPorts ins)) : Option (SubZero.Opcode [] out) :=
  (arithmeticRules op).replacement? known operands

abbrev binaryLiteral? (known : Literals args past) (op : SubZero.BinaryOpcode)
    (operands : Wires args past (dataPorts [word, word])) : Option (SubZero.Opcode [] word) :=
  literal? known op operands

abbrev foldDataflow (known : Literals args past) (flow : Dataflow SubZero.Opcode args past sigs) :
    Dataflow SubZero.Opcode args past sigs :=
  Scan.foldDataflow arithmeticRules known flow

/-- Normalize the native arithmetic program with no assumptions about its arguments. -/
def fold (program : Program SubZero.Opcode inputs out) : Program SubZero.Opcode inputs out :=
  Scan.fold arithmeticRules program

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold
