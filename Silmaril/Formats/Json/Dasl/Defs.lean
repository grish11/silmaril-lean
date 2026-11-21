module
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Digits.Defs
public import Silmaril.Formats.Dasl.Presentation.Defs
public import Silmaril.Formats.JsonWire.Defs
public import Silmaril.Formats.JsonWithBytes.Defs

@[expose] public section
namespace Silmaril.Formats.JsonDasl
open Dasl Dasl.Encode

/-- The numeric safe-integer bound. This alone does not impose I-JSON's
string repertoire or unique-key requirement. -/
def IsSafe (number : Int64) : Prop := number.toInt.natAbs ≤ 9007199254740991

abbrev SafeInt := { number : Int64 // IsSafe number }

abbrev SafeJson := JsonWire.Ast SafeInt
abbrev I64Json := JsonWire.Ast Int64
abbrev RfcJson := JsonWire.Ast JsonWire.Decimal

/-- A typed, in-memory byte extension of the same raw AST. It retains UTF-16
code units even when no Unicode scalar string would represent them. -/
abbrev BytesAst (Number : Type) := KeyedRawJson JsonWire.Units (JsonWire.Scalar Number ⊕ ByteArray)
abbrev SafeJsonBytes := BytesAst SafeInt
abbrev I64JsonBytes := BytesAst Int64
abbrev RfcJsonBytes := BytesAst JsonWire.Decimal

def includeBytes {Number : Type} (ast : JsonWire.Ast Number) : BytesAst Number := ast.mapScalar Sum.inl

def i64Number? (number : Int) : Option Int64 :=
  if -(2 ^ 63) ≤ number ∧ number < 2 ^ 63 then some (Int64.ofInt number) else none

/-- Value-based integral profile: `1e2` and `100` agree; overflow and nonintegral values fail. -/
def parseI64? (input : Bytes) : Option I64Json := do
  let ast ← JsonWire.parseInteger? input
  JsonWire.mapNumbers? i64Number? ast

def safe? (number : Int64) : Option SafeInt :=
  if safe : number.toInt.natAbs ≤ 9007199254740991 then some ⟨number, safe⟩ else none

def parseSafe? (input : Bytes) : Option SafeJson :=
  (parseI64? input).bind (JsonWire.mapNumbers? safe?)

def syntaxPER {Wire Ast : Type} (parse : Wire → Option Ast) : PER Wire := PER.ofDecoder parse

def astPER (Ast : Type) : PER Ast := PER.equality Ast

def unitCodec : TotalCodec UInt16 Value :=
  ⟨(fun unit => .i64 unit.toUInt64),
    (fun | .i64 bits => if bits.toNat < 65536 then some bits.toUInt16 else none | _ => none),
    fun unit => by
      have bound : unit.toNat < 65536 := unit.toNat_lt
      simp [bound]⟩

def unitsCodec : TotalCodec JsonWire.Units Value := listOf unitCodec

def encodeNat (value : Nat) : Value :=
  (listOf bits).encode ((Nat.digits 256 value).map UInt64.ofNat)

def decodeNat? (value : Value) : Option Nat :=
  ((listOf bits).decode? value).map fun digits => Nat.ofDigits 256 (digits.map UInt64.toNat)

def encodeInt : Int → Value
  | .ofNat magnitude => .list 2 ![.bool false, encodeNat magnitude]
  | .negSucc magnitude => .list 2 ![.bool true, encodeNat magnitude]

def decodeInt? : Value → Option Int
  | .list 2 children => do
    let negative ← boolean.decode? (children 0)
    let magnitude ← decodeNat? (children 1)
    pure (if negative then .negSucc magnitude else .ofNat magnitude)
  | _ => none

def encodeDecimal (number : JsonWire.Decimal) : Value :=
  .list 3 ![.bool number.negative, encodeNat number.coefficient, encodeInt number.exponent]

def decodeDecimal? : Value → Option JsonWire.Decimal
  | .list 3 children => do
    pure ⟨← boolean.decode? (children 0), ← decodeNat? (children 1), ← decodeInt? (children 2)⟩
  | _ => none

def safeCodec : TotalCodec SafeInt Value :=
  ⟨(fun number => signed.encode number.val), (fun tree => signed.decode? tree |>.bind safe?),
    fun ⟨number, safe⟩ => by
      change (signed.decode? (signed.encode number)).bind safe? = _
      rw [signed.recovers]
      have bound : number.toInt.natAbs ≤ 9007199254740991 := safe
      simp [safe?, bound]⟩

def encodeScalar {N : Type} (numbers : TotalCodec N Value) : JsonWire.Scalar N → Value
  | none => .null
  | some (.bool value) => .bool value
  | some (.string value) => .list 2 ![.string "json:utf16", unitsCodec.encode value]
  | some (.number value) => .list 2 ![.string "json:number", numbers.encode value]

def decodeScalar? {N : Type} (numbers : TotalCodec N Value) : Value → Option (JsonWire.Scalar N)
  | .null => some none
  | .bool value => some (some (.bool value))
  | .list 2 children =>
    match children 0 with
    | .string "json:utf16" => (unitsCodec.decode? (children 1)).map (some ∘ JsonWire.Atom.string)
    | .string "json:number" => (numbers.decode? (children 1)).map (some ∘ JsonWire.Atom.number)
    | _ => none
  | _ => none

def encodeBytesScalar {N : Type} (numbers : TotalCodec N Value) : JsonWire.Scalar N ⊕ ByteArray → Value
  | .inl value => encodeScalar numbers value
  | .inr value => .bytes value

def decodeBytesScalar? {N : Type} (numbers : TotalCodec N Value) : Value → Option (JsonWire.Scalar N ⊕ ByteArray)
  | .bytes value => some (.inr value)
  | tree => (decodeScalar? numbers tree).map Sum.inl

def encodeOrderedScalar {N : Type} (numbers : TotalCodec N Value) : JsonWithBytes.Scalar N → Value
  | .null => .null
  | .bool value => .bool value
  | .string value => .string value
  | .number value => .list 1 ![numbers.encode value]
  | .bytes value => .bytes value.toByteArray

def decodeOrderedScalar? {N : Type} (numbers : TotalCodec N Value) : Value → Option (JsonWithBytes.Scalar N)
  | .null => some .null
  | .bool value => some (.bool value)
  | .string value => some (.string value)
  | .list 1 children => (numbers.decode? (children 0)).map .number
  | .bytes value => some (.bytes value.data.toList)
  | _ => none

/-- Tagged value nodes; object tails are ordered key/value cons cells, not DASL dicts. -/
def encodeRaw {Key Scalar : Type} (keys : TotalCodec Key Value) (scalar : TotalCodec Scalar Value) :
    {sort : JsonIx} → RawSyn Key Scalar sort → Value
  | _, .scalar value => .list 2 ![.string "json:scalar", scalar.encode value]
  | _, .list tail => .list 2 ![.string "json:array", encodeRaw keys scalar tail]
  | _, .map tail => .list 2 ![.string "json:object", encodeRaw keys scalar tail]
  | _, .nil => .null
  | _, .cons head tail => .list 2 ![encodeRaw keys scalar head, encodeRaw keys scalar tail]
  | _, .objNil => .null
  | _, .objCons key value tail => .list 3 ![keys.encode key, encodeRaw keys scalar value, encodeRaw keys scalar tail]

def decodeRaw? {Key Scalar : Type} (keys : TotalCodec Key Value) (scalar : TotalCodec Scalar Value)
    (sort : JsonIx) (tree : Value) : Option (RawSyn Key Scalar sort) :=
  match sort, tree with
  | .val, .list 2 children =>
    match children 0 with
    | .string "json:scalar" => (scalar.decode? (children 1)).map .scalar
    | .string "json:array" => (decodeRaw? keys scalar .arr (children 1)).map .list
    | .string "json:object" => (decodeRaw? keys scalar .obj (children 1)).map .map
    | _ => none
  | .arr, .null => some .nil
  | .arr, .list 2 children => do
    pure (.cons (← decodeRaw? keys scalar .val (children 0)) (← decodeRaw? keys scalar .arr (children 1)))
  | .obj, .null => some .objNil
  | .obj, .list 3 children => do
    pure (.objCons (← keys.decode? (children 0)) (← decodeRaw? keys scalar .val (children 1))
      (← decodeRaw? keys scalar .obj (children 2)))
  | _, _ => none
termination_by structural tree

end Silmaril.Formats.JsonDasl
