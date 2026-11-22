module

public import Silmaril.Formats.Dasl.Resolve.Defs
public import Silmaril.Semantics.Naming.Lift.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Lift

open Silmaril.Semantics.Naming (Relation)
open Silmaril.Semantics.Naming.Lift (Coordinate)

variable {Name Item : Type}

/-- A direct DASL value interpreted by a supplied representation relation. -/
def value (decode : Relation Value Item) : Coordinate := .encoded decode

/-- A heterogeneous tuple of decoders with the same abstract DASL surface. -/
inductive ValueDecoders : List Type → Type 1 where
  | nil : ValueDecoders []
  | cons {item : Type} {rest : List Type} (decode : Relation Value item) (decoders : ValueDecoders rest) :
      ValueDecoders (item :: rest)

def ValueDecoders.coordinates : {types : List Type} → ValueDecoders types → List Coordinate
  | _, .nil => []
  | _, .cons decode rest => value decode :: rest.coordinates

def ValueDecoders.lift {types : List Type} (decoders : ValueDecoders types)
    (predicate : Silmaril.Semantics.Naming.Lift.Args decoders.coordinates → Prop) :
    Silmaril.Semantics.Naming.Lift.Inputs decoders.coordinates → Prop :=
  Silmaril.Semantics.Naming.Lift.rel predicate

/-- An abstract object root, with a finite full expansion that represents the item. -/
def name (store : Store Name) (decode : Relation Value Item) : Coordinate :=
  .named (ValueNames store) decode

def namesWhere (store : Store Name) (decode : Relation Value Item) (predicate : Item → Prop) : Set Name :=
  Silmaril.Semantics.Naming.Lift.where_ (name store decode) predicate

/-- `i64` is a signed word. A natural number fits iff it is strictly below `2^63`. -/
def natI64 (repr : Value) (number : Nat) : Prop :=
  repr = .i64 (UInt64.ofNat number) ∧ number < 2^63

def lengthNat (ctx : Coordinate) (length : ctx.Meaning → Nat) (root : ctx.Surface) (size : Nat) : Prop :=
  Silmaril.Semantics.Naming.Lift.rel (coordinates := [ctx, .direct Nat])
    (fun args => length args.1 = args.2.1) (root, size, ())

def lengthI64 (ctx : Coordinate) (length : ctx.Meaning → Nat) (root : ctx.Surface) (size : Value) : Prop :=
  Silmaril.Semantics.Naming.Lift.rel (coordinates := [ctx, value natI64])
    (fun args => length args.1 = args.2.1) (root, size, ())

end Silmaril.Formats.Dasl.Lift
