module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.WIT

universe u

variable {Ref : Type u}

/-- Fixed-width WIT primitives: integers, floats, `bool` and `char`. `string` is a
primitive but not a scalar in this fragment. This is wider than the integer-word
fragment of the canonical ABI loader. -/
def ScalarType := { prim : Primitive // prim ≠ .string }

def ScalarType.ofPrimitive (prim : Primitive) : Option ScalarType :=
  if scalar : prim ≠ .string then some ⟨prim, scalar⟩ else none

/-- Interpret a scalar using the same payload type as the general WIT adapter. -/
def ScalarType.pty (scalar : ScalarType) : PTy := ofPrim scalar.val

def ScalarType.toWit (scalar : ScalarType) : WIT.ValType Ref Nat := .prim scalar.val

def ScalarType.ofWit : WIT.ValType Ref Nat → Option ScalarType
  | .prim prim => ofPrimitive prim
  | _ => none

def ScalarType.ofPayload (type : PTy) : Option ScalarType := ofWit (Wit.toWit (Ref := Empty) type)

/-- A represented compound constructor at the root. This classification says nothing
about whether its members contain resources, or whether the signature is well formed. -/
def isCompound : PTy → Bool
  | .list _ | .fixedList _ _ | .record _ | .tuple _ | .variant _ | .enum _
  | .option _ | .result _ _ | .flags _ => true
  | _ => false

/-- Compounds in the resolved acceptor fragment. Children use the shared `PTy`
syntax, so e.g. a record can contain a scalar, a string, a list or a resource field.
The checked host separately decides which of these can be stored. -/
def CompoundType := { type : PTy // isCompound type = true }

namespace CompoundType

def pty (compound : CompoundType) : PTy := compound.val

def list (element : PTy) : CompoundType := ⟨.list element, rfl⟩
def fixedList (element : PTy) (length : Nat) : CompoundType := ⟨.fixedList element length, rfl⟩
def record (fields : List (String × PTy)) : CompoundType := ⟨.record fields, rfl⟩
def tuple (fields : List PTy) : CompoundType := ⟨.tuple fields, rfl⟩
def variant (cases : List (String × Option PTy)) : CompoundType := ⟨.variant cases, rfl⟩
def enum (cases : List String) : CompoundType := ⟨.enum cases, rfl⟩
def flags (labels : List String) : CompoundType := ⟨.flags labels, rfl⟩
def option (element : PTy) : CompoundType := ⟨.option element, rfl⟩
def result (ok error : Option PTy) : CompoundType := ⟨.result ok error, rfl⟩

def ofPayload (type : PTy) : Option CompoundType :=
  if compound : isCompound type = true then some ⟨type, compound⟩ else none

def toWit (compound : CompoundType) : WIT.ValType Ref Nat := Wit.toWit compound.pty

def ofWit (type : WIT.ValType Ref Nat) : Option CompoundType :=
  (Wit.ofWit type).bind ofPayload

end CompoundType

/-- A payload-restricted signature uses the same ASTs and writer semantics after
embedding its fields. It does not define a second acceptor protocol. -/
structure FragmentSig (Field : Type) where
  Tag : Type
  params : Tag → List Field
  arity : Tag → Arity

abbrev FragmentSig.embed {Field : Type} (signature : FragmentSig Field) (pty : Field → PTy) :
    WitSig :=
  ⟨signature.Tag, fun tag => (signature.params tag).map pty, signature.arity⟩

abbrev ScalarSig := FragmentSig ScalarType
abbrev CompoundSig := FragmentSig CompoundType

abbrev ScalarSig.toWitSig (signature : ScalarSig) : WitSig := signature.embed ScalarType.pty
abbrev CompoundSig.toWitSig (signature : CompoundSig) : WitSig := signature.embed CompoundType.pty

end Silmaril.Wasm.Game.HandleAccept.Wit
