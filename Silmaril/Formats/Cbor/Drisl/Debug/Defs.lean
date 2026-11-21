module

public import Silmaril.Formats.Cbor.Drisl.Ast.Defs
public import Silmaril.Encoding.Base64

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl.Debug

inductive Escape where
  | none | suffix | prefix
  deriving DecidableEq, Repr

def Escape.keyChars : Escape → List Char → List Char
  | .prefix, '$' :: tail => '$' :: '$' :: tail
  | .suffix, '$' :: tail => '$' :: (tail ++ ['$'])
  | _, chars => chars

def Escape.readKeyChars? : Escape → List Char → Option (List Char)
  | .none, chars => some chars
  | .prefix, '$' :: '$' :: tail => some ('$' :: tail)
  | .prefix, '$' :: _ => Option.none
  | .suffix, '$' :: tail => match tail.reverse with
    | '$' :: rest => some ('$' :: rest.reverse)
    | _ => Option.none
  | _, chars => some chars

def Escape.key (policy : Escape) (name : String) : String :=
  String.ofList (policy.keyChars name.toList)

def Escape.readKey? (policy : Escape) (name : String) : Option String :=
  String.ofList <$> policy.readKeyChars? name.toList

inductive Wrapper where
  | bytes | link
  deriving DecidableEq, Repr

def Wrapper.key : Wrapper → String
  | .bytes => "$bytes"
  | .link => "$link"

def Wrapper.ofKey? (name : String) : Option Wrapper :=
  if name = Wrapper.bytes.key then some .bytes
  else if name = Wrapper.link.key then some .link else none

inductive Atom (Numeric : Type) where
  | null
  | bool (value : Bool)
  | string (value : String)
  | number (value : Numeric)
  deriving DecidableEq, Repr

abbrev Tree (Numeric : Type := JsonWire.Decimal) := RawJson (Atom Numeric)

structure Codec (Input Number Link : Type) where
  number : Input → Number
  readNumber? : Number → Option Input
  link : Link → String
  readLink? : String → Option Link

def wrap {Numeric : Type} (tag : Wrapper) (value : String) : Tree Numeric :=
  .map (.objCons tag.key (.scalar (.string value)) .objNil)

def wrapper? {Numeric : Type} (fields : RawSyn String (Atom Numeric) .obj) :
    Option (Wrapper × Tree Numeric) :=
  match fields with
  | .objCons name value .objNil => (Wrapper.ofKey? name).map (·, value)
  | _ => none

/-- Structural debug representation. Shape and member order are retained;
escaped object order need not be lexicographically sorted. -/
def encode {Input Numeric Link : Type} (codec : Codec Input Numeric Link) (policy : Escape) :
    {index : JsonIx} → RawSyn String (Scalar Input Link) index → RawSyn String (Atom Numeric) index
  | _, .scalar (.data .null) => .scalar .null
  | _, .scalar (.data (.bool value)) => .scalar (.bool value)
  | _, .scalar (.data (.string value)) => .scalar (.string value)
  | _, .scalar (.data (.number value)) => .scalar (.number (codec.number value))
  | _, .scalar (.data (.bytes value)) => wrap .bytes (Base64.encode Base64.Alphabet.std false value)
  | _, .scalar (.link cid) => wrap .link (codec.link cid)
  | _, .map fields => .map (encode codec policy fields)
  | _, .list items => .list (encode codec policy items)
  | _, .nil => .nil
  | _, .cons value tail => .cons (encode codec policy value) (encode codec policy tail)
  | _, .objNil => .objNil
  | _, .objCons name value tail => .objCons (policy.key name)
      (encode codec policy value) (encode codec policy tail)

def readWrapper? {Input Numeric Link : Type} (codec : Codec Input Numeric Link)
    (tag : Wrapper) (value : Tree Numeric) : Option (RawJson (Scalar Input Link)) :=
  match tag, value with
  | .bytes, .scalar (.string text) =>
    (fun bytes => .scalar (.data (.bytes bytes))) <$> Base64.decode? Base64.Alphabet.std false text
  | .link, .scalar (.string text) => (.scalar ∘ Scalar.link) <$> codec.readLink? text
  | _, _ => none

/-- A reserved singleton is always a wrapper, even if its payload is malformed.
In escaped modes every other dollar-prefixed field must be a canonical escape. -/
def decode? {Input Numeric Link : Type} (codec : Codec Input Numeric Link) (policy : Escape) :
    {index : JsonIx} → RawSyn String (Atom Numeric) index → Option (RawSyn String (Scalar Input Link) index)
  | _, .scalar .null => some (.scalar (.data .null))
  | _, .scalar (.bool value) => some (.scalar (.data (.bool value)))
  | _, .scalar (.string value) => some (.scalar (.data (.string value)))
  | _, .scalar (.number value) => (.scalar ∘ Scalar.data ∘ JsonWithBytes.Scalar.number) <$>
      codec.readNumber? value
  | _, .map fields => match wrapper? fields with
    | some (tag, value) => readWrapper? codec tag value
    | none => .map <$> decode? codec policy fields
  | _, .list items => .list <$> decode? codec policy items
  | _, .nil => some .nil
  | _, .cons value tail => return .cons (← decode? codec policy value) (← decode? codec policy tail)
  | _, .objNil => some .objNil
  | _, .objCons name value tail =>
    return .objCons (← policy.readKey? name) (← decode? codec policy value) (← decode? codec policy tail)

def SafeObject {Atom : Type} (policy : Escape) : RawSyn String Atom .obj → Prop
  | .objCons name _ .objNil => Wrapper.ofKey? (policy.key name) = none
  | _ => True

/-- Exact structural collision domain. Multi-field objects may contain reserved
names in no-escape mode. A reserved singleton is excluded regardless of payload. -/
def CollisionFree {Numeric Link : Type} (policy : Escape) :
    {index : JsonIx} → RawSyn String (Scalar Numeric Link) index → Prop
  | _, .map fields => SafeObject policy fields ∧ CollisionFree policy fields
  | _, .list items => CollisionFree policy items
  | _, .cons value tail | _, .objCons _ value tail => CollisionFree policy value ∧ CollisionFree policy tail
  | _, _ => True

/-- A recursive predicate on ordinary field names, including names in arrays. -/
def KeysSatisfy {Key Atom : Type} (allowed : Key → Prop) :
    {index : JsonIx} → RawSyn Key Atom index → Prop
  | _, .scalar _ | _, .nil | _, .objNil => True
  | _, .list items | _, .map items => KeysSatisfy allowed items
  | _, .cons value tail => KeysSatisfy allowed value ∧ KeysSatisfy allowed tail
  | _, .objCons name value tail => allowed name ∧ KeysSatisfy allowed value ∧ KeysSatisfy allowed tail

def NoReserved (name : String) : Prop := Wrapper.ofKey? name = none
def NoDollar (name : String) : Prop := ∀ tail, name.toList ≠ '$' :: tail

end Silmaril.Formats.Cbor.Drisl.Debug
