module

public import Silmaril.SSA.SeaOfNodes.Pure.SubZero.Defs

/-! Structural word value numbers over native, acyclic producer prefixes. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.WordNumber

open Diamond (Model Ty Val ValueSort dataPorts)
open Pure.SubZero (BinaryOpcode Opcode word wordPort)
open RVSDG (Port Tuple)

variable {args : List (Ty Unit)}

/-- A word's structural value number with exact typed argument positions,
literal payloads and ordered child numbers. -/
inductive Key (args : List (Ty Unit)) where
  | argument (port : Port args wordPort)
  | literal (value : BitVec 64)
  | binary (op : BinaryOpcode) (lhs rhs : Key args)

/-- Compare the complete producer expressions recursively. -/
def Key.matches : Key args → Key args → Bool
  | .argument lhs, .argument rhs => decide (lhs.index = rhs.index)
  | .literal lhs, .literal rhs => decide (lhs = rhs)
  | .binary lop lhs rhs, .binary rop otherLhs otherRhs =>
    decide (lop = rop) && lhs.matches otherLhs && rhs.matches otherRhs
  | _, _ => false

/-- Replace typed argument leaves, preserving every literal and ordered opcode. -/
def Key.substitute (argument : Port args wordPort → Key args) : Key args → Key args
  | .argument port => argument port
  | .literal bits => .literal bits
  | .binary op lhs rhs => .binary op (lhs.substitute argument) (rhs.substitute argument)

/-- Interpret a structural number under a concrete typed entry. -/
def Key.eval (entry : Tuple (Val Pure.SubZero.model.value) args) : Key args → BitVec 64
  | .argument port => entry.get port
  | .literal value => value
  | .binary op lhs rhs => Pure.SubZero.model.run op (.cons (lhs.eval entry) (.cons (rhs.eval entry) .nil))

/-- The existing producer evaluation order constructs keys from previously
numbered inputs. Predicate entries play no role in the word-only signature. -/
def numbering (args : List (Ty Unit)) : Model Opcode where
  value _ := Key args
  run
    | .literal value, .nil => .literal value
    | .sub, .cons lhs (.cons rhs .nil) => .binary .sub lhs rhs
    | .add, .cons lhs (.cons rhs .nil) => .binary .add lhs rhs
    | .mul, .cons lhs (.cons rhs .nil) => .binary .mul lhs rhs

/-- Seed a typed slice using its embedding in the full argument bank. -/
def keyArguments (args : List (Ty Unit)) : (inputs : List (ValueSort Unit)) →
    (∀ {sort}, Port (dataPorts inputs) (.value sort) → Port args (.value sort)) →
    Tuple (Val (numbering args).value) (dataPorts inputs)
  | [], _ => .nil
  | .predicate :: rest, lift =>
    .cons ⟨false⟩ (keyArguments args rest (fun port => lift (.tail port)))
  | .data () :: rest, lift =>
    .cons (.argument (lift .head)) (keyArguments args rest (fun port => lift (.tail port)))

/-- Seed every word input with its original typed argument position. -/
def entryKeys (inputs : List (ValueSort Unit)) :
    Tuple (Val (numbering (dataPorts inputs)).value) (dataPorts inputs) :=
  keyArguments (dataPorts inputs) inputs (fun port => port)

end Silmaril.SSA.SeaOfNodes.GVN.WordNumber
