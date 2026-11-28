module

public import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Defs

/-! Append-only interning of ordered word producer signatures. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern

open Diamond (Dataflow Ty Val ValueSort dataPorts sortValue)
open Pure.SubZero (BinaryOpcode Opcode wordPort)
open RVSDG (Locals Origin Port Tuple Wires extend)

abbrev Id := Nat

/-- All signatures are for words. Binary inputs are ordered IDs in the
same table; argument indices count positions in the actual typed bank. -/
inductive Signature where
  | argument (index : Nat)
  | literal (value : BitVec 64)
  | binary (op : BinaryOpcode) (lhs rhs : Id)
  deriving DecidableEq

abbrev Table := List Signature

/-- Return a stable ID, appending a signature only when it is new. -/
def intern (table : Table) (signature : Signature) : Table × Id :=
  match table.findIdx? (fun existing => decide (existing = signature)) with
  | some id => (table, id)
  | none => (table ++ [signature], table.length)

/-- The meaning of an ID in one table. This relation is used only
in proofs; the executable evaluator stores signatures and IDs. -/
inductive Decodes {args : List (Ty Unit)} (table : Table) : Id → Key args → Prop where
  | argument {id : Id} {port : Port args wordPort}
      (found : table[id]? = some (.argument port.index)) : Decodes table id (.argument port)
  | literal {id : Id} {value : BitVec 64}
      (found : table[id]? = some (.literal value)) : Decodes table id (.literal value)
  | binary {id leftId rightId : Id} {op : BinaryOpcode} {lhs rhs : Key args}
      (found : table[id]? = some (.binary op leftId rightId))
      (left : Decodes table leftId lhs) (right : Decodes table rightId rhs) :
      Decodes table id (.binary op lhs rhs)

abbrev IdVal := Val (fun _ : Unit => Id)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}

def readId (entry : Tuple IdVal args) (locals : Locals IdVal past) (wire : Origin args past wordPort) : Id :=
  (Wires.read (.cons wire .nil) entry locals).get .head

def internOp (table : Table) : {ins : List (ValueSort Unit)} → {out : ValueSort Unit} →
    Opcode ins out → Tuple IdVal (dataPorts ins) → Table × sortValue (fun _ : Unit => Id) out
  | _, _, .literal value, .nil => intern table (.literal value)
  | _, _, .add, .cons lhs (.cons rhs .nil) => intern table (.binary .add lhs rhs)
  | _, _, .sub, .cons lhs (.cons rhs .nil) => intern table (.binary .sub lhs rhs)
  | _, _, .mul, .cons lhs (.cons rhs .nil) => intern table (.binary .mul lhs rhs)

/-- Keep the native topological evaluation order, interning each binding
after the IDs of its typed operands are available. -/
def eval (entry : Tuple IdVal args) : {past sigs : List (List (Ty Unit))} →
    Dataflow Opcode args past sigs → Table → Locals IdVal past → Table × Locals IdVal (extend past sigs)
  | _, _, .nil, table, locals => (table, locals)
  | scope, _, .cons (sigs := tail) (out := out) op wires rest, table, locals =>
    let result := internOp table op (wires.read entry locals)
    eval entry (past := scope ++ [[.value out]]) (sigs := tail) rest result.1
      (locals.snoc (head := [.value out]) (Tuple.cons (F := IdVal) (t := .value out) result.2 .nil))

/-- Number each word argument using its embedding in the root argument bank. -/
def seed : (inputs : List (ValueSort Unit)) →
    (∀ {sort}, Port (dataPorts inputs) (.value sort) → Port args (.value sort)) →
    Table → Table × Tuple IdVal (dataPorts inputs)
  | [], _, table => (table, .nil)
  | .predicate :: rest, lift, table =>
    let (final, tail) := seed rest (fun port => lift (.tail port)) table
    (final, .cons ⟨false⟩ tail)
  | .data () :: rest, lift, table =>
    let (next, id) := intern table (.argument (lift .head).index)
    let (final, tail) := seed rest (fun port => lift (.tail port)) next
    (final, .cons id tail)

/-- Start a fresh namespace, shared by the entry and every subsequent cut. -/
def entryIds (inputs : List (ValueSort Unit)) : Table × Tuple IdVal (dataPorts inputs) :=
  seed (args := dataPorts inputs) inputs (fun port => port) []

/-- Typed prefix IDs denote the corresponding structural word keys. -/
def Agrees (table : Table) (entry : Tuple IdVal args) (locals : Locals IdVal past)
    (keys : Tuple (Val (numbering args).value) args) (numbered : Locals (Val (numbering args).value) past) :
    Prop :=
  ∀ wire : Origin args past wordPort,
    Decodes table (readId entry locals wire) (Diamond.read (numbering args) wire keys numbered)

end Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern
