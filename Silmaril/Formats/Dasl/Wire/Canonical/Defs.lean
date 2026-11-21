module

public import Silmaril.Formats.Dasl.Wire.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Wire

open Silmaril.Formats.Cbor

/-- The same key comparison used by the canonical DRISL emitter, including
the CBOR text-length head. It is not lexical order on `String`. -/
def keyLE (left right : String) : Bool :=
  !Drisl.lexLt (Drisl.utf8Value right).encode (Drisl.utf8Value left).encode

/-- A witness for the recursively sorted ordered syntax produced by the
canonical writer. No fields, scalar values, or typed links are rewritten. -/
def canonicalOrder {Name : Type} : {index : JsonIx} → RawSyn String (Drisl.Scalar Int64 (Link Name)) index →
    RawSyn String (Drisl.Scalar Int64 (Link Name)) index
  | _, .scalar atom => .scalar atom
  | _, .list items => .list (canonicalOrder items)
  | _, .map fields => .map (.ofEntries ((canonicalOrder fields).toEntries.mergeSort fun left right => keyLE left.1 right.1))
  | _, .nil => .nil
  | _, .cons head tail => .cons (canonicalOrder head) (canonicalOrder tail)
  | _, .objNil => .objNil
  | _, .objCons key head tail => .objCons key (canonicalOrder head) (canonicalOrder tail)

def canonicalModel (value : Shallow Cid) : Cbor.Value := Drisl.emitModel Drisl.i64Cbor cidCodec true (toOrdered value)

namespace Bounds

mutual

def value : (model : Cbor.Value) → Decidable model.Encodable
  | .uint amount | .nint amount => inferInstanceAs (Decidable (amount < 2 ^ 64))
  | .bytes bytes | .text bytes => inferInstanceAs (Decidable (bytes.length < 2 ^ 64))
  | .array items =>
    letI := itemsBound items
    inferInstanceAs (Decidable (items.length < 2 ^ 64 ∧ ListEncodable items))
  | .map fields =>
    letI := fieldsBound fields
    inferInstanceAs (Decidable (fields.length < 2 ^ 64 ∧ MapEncodable fields))
  | .tag tag payload =>
    letI := value payload
    inferInstanceAs (Decidable (tag < 2 ^ 64 ∧ payload.Encodable))
  | .simple amount => inferInstanceAs (Decidable (amount < 24 ∨ (32 ≤ amount ∧ amount < 256)))
  | .float width bits => inferInstanceAs (Decidable ((width = 2 ∨ width = 4 ∨ width = 8) ∧ bits < 256 ^ width))
termination_by structural model => model

def itemsBound : (items : List Cbor.Value) → Decidable (ListEncodable items)
  | [] => isTrue trivial
  | item :: tail =>
    letI := value item
    letI := itemsBound tail
    inferInstanceAs (Decidable (item.Encodable ∧ ListEncodable tail))
termination_by structural items => items

def fieldsBound : (fields : List (Cbor.Value × Cbor.Value)) → Decidable (MapEncodable fields)
  | [] => isTrue trivial
  | (key, payload) :: tail =>
    letI := value key
    letI := value payload
    letI := fieldsBound tail
    inferInstanceAs (Decidable (key.Encodable ∧ payload.Encodable ∧ MapEncodable tail))
termination_by structural fields => fields

end

end Bounds

/-- Check the model's actual CBOR length and argument bounds before calling
the existing writer. On the checked domain the abstract value is recoverable. -/
def renderBounded? (value : Shallow Cid) : Option ByteArray :=
  letI := Bounds.value (canonicalModel value)
  if (canonicalModel value).Encodable then render? value else none

end Silmaril.Formats.Dasl.Wire
