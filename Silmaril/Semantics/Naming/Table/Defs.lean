module

public import Silmaril.Semantics.Naming.Defs

/-! Sparse radix tables for finite observations. A caller chooses how to route abstract
names. The routing function does not need to be a hash, and lookup does not validate one. -/

@[expose] public section

namespace Silmaril.Semantics.Naming

inductive Table (Payload : Type) where
  | empty
  | node (slot : Option Payload) (zero one : Table Payload)

namespace Table

variable {Name Payload : Type}

/-- Fixed-width, most-significant bit first, with no delimiter ambiguity. -/
def byteRoute (bytes : List UInt8) : List Bool :=
  bytes.flatMap fun byte => (List.range 8).map fun offset => byte.toNat.testBit (7 - offset)

/-- Move at most one edge per bit; a key can end at an internal node. -/
def lookup : Table Payload → List Bool → Option Payload
  | .empty, _ => none
  | .node slot _ _, [] => slot
  | .node _ zero _, false :: rest => zero.lookup rest
  | .node _ _ one, true :: rest => one.lookup rest

/-- The structural observations of a trie, independent of executable lookup. -/
inductive Entry : Table Payload → List Bool → Payload → Prop where
  | here {payload : Payload} {zero one : Table Payload} :
      Entry (.node (some payload) zero one) [] payload
  | zero {slot : Option Payload} {zero one : Table Payload} {route : List Bool} {payload : Payload} :
      Entry zero route payload → Entry (.node slot zero one) (false :: route) payload
  | one {slot : Option Payload} {zero one : Table Payload} {route : List Bool} {payload : Payload} :
      Entry one route payload → Entry (.node slot zero one) (true :: route) payload

/-- Replace the slot at one route. Data import must decide separately whether to allow
replacement. Noninjective routing aliases names, even when the table is binding. -/
def set : List Bool → Payload → Table Payload → Table Payload
  | [], payload, .empty => .node (some payload) .empty .empty
  | [], payload, .node _ zero one => .node (some payload) zero one
  | false :: rest, payload, .empty => .node none (set rest payload .empty) .empty
  | true :: rest, payload, .empty => .node none .empty (set rest payload .empty)
  | false :: rest, payload, .node slot zero one => .node slot (set rest payload zero) one
  | true :: rest, payload, .node slot zero one => .node slot zero (set rest payload one)

def relation (table : Table Payload) (route : Name → List Bool) : Relation Name Payload :=
  fun name payload => Entry table (route name) payload

def namesOf (rel : Relation Name Payload) (payload : Payload) : Set Name :=
  { name | rel name payload }

/-- Left-biased lookup. Only compatible overlaps give a lookup for the union relation. -/
def overlay (left right : Name → Option Payload) (name : Name) : Option Payload :=
  (left name).orElse (fun () => right name)

def Compatible (left right : Name → Option Payload) : Prop :=
  ∀ ⦃name first second⦄, left name = some first → right name = some second → first = second

end Table
end Silmaril.Semantics.Naming
