module

public import Silmaril.Semantics.SQLite.Relational.Value.Defs
public import Init.Data.String.Search

/-! A bounded column-write affinity model for already constructed SQL values. -/

@[expose] public section

namespace Silmaril.SQLite.Relational

inductive Affinity where
  | integer | real | numeric | text | blob
  deriving DecidableEq, Repr

/-- Ordinary declared type names use ASCII-insensitive substring rules in precedence order.
The input is the resolved, NUL-free type name (`none` for no declaration), after parsing SQL. -/
def Affinity.ofDeclaredType : Option String → Affinity
  | none => .blob
  | some name =>
    let name := name.toLower
    if name.contains "int" then .integer
    else if name.contains "char" || name.contains "clob" || name.contains "text" then .text
    else if name.contains "blob" then .blob
    else if name.contains "real" || name.contains "floa" || name.contains "doub" then .real
    else .numeric

inductive StrictType where
  | int | integer | real | text | blob | any
  deriving DecidableEq, Repr

/-- STRICT accepts just the six built-in declared names (ASCII case-insensitive). -/
def StrictType.ofDeclaredType (name : Option String) : Option StrictType :=
  match name.map String.toLower with
  | some "int" => some .int
  | some "integer" => some .integer
  | some "real" => some .real
  | some "text" => some .text
  | some "blob" => some .blob
  | some "any" => some .any
  | _ => none

/-- Affinity used at the STRICT write boundary. ANY has the identity affinity. -/
def StrictType.affinity : StrictType → Affinity
  | .int | .integer => .integer
  | .real => .real
  | .text => .text
  | .blob | .any => .blob

/-- Test the storage class after affinity, independently of row constraints. -/
def StrictType.accepts : StrictType → StorageClass → Bool
  | _, .null | .any, _ => true
  | .int, .integer | .integer, .integer | .real, .real | .text, .text | .blob, .blob => true
  | _, _ => false

inductive ColumnType where
  | ordinary (affinity : Affinity)
  | strict (type : StrictType)
  deriving DecidableEq, Repr

/-- Reasons that the affinity model leaves a conversion unspecified. -/
inductive UnsupportedConversion where
  | numericTextEncoding | numericTextNul | numericTextRealSyntax | numericTextOverflow | realToText
  deriving DecidableEq, Repr

inductive AffinityError where
  /-- A conversion outside this model's profile. -/
  | unsupported (conversion : UnsupportedConversion)
  /-- A STRICT storage class mismatch after a supported conversion. -/
  | datatype (declared : StrictType) (actual : StorageClass)
  deriving DecidableEq, Repr

/-- Apply ordinary column affinity, observing the logical storage class on readback. REAL
uses binary64 round-to-nearest, ties-to-even for promotion from INTEGER. -/
def Affinity.apply : Affinity → SqlValue → Except AffinityError SqlValue
  | .integer, value | .numeric, value => applyNumeric value
  | .real, value => do
    match ← applyNumeric value with
    | .integer i => return .ofRealBits (Float.Model.ofInt64 i).toBits
    | value => return value
  | .text, .integer i => .ok (.text (.utf8 (toString i.toInt)))
  | .text, .real _ => .error (.unsupported .realToText)
  | _, value => .ok value
where
  isSpace (b : UInt8) : Bool := b == 32 || (9 ≤ b && b ≤ 13)
  isDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

  splitSign : List UInt8 → Bool × List UInt8
    | 45 :: rest => (true, rest)
    | 43 :: rest => (false, rest)
    | bytes => (false, bytes)

  realSyntax (digits : List UInt8) (rest : List UInt8) : Bool :=
    let (fraction, tail) := match rest with
      | 46 :: tail => tail.span isDigit
      | tail => ([], tail)
    let validExponent := match tail with
      | 69 :: exp | 101 :: exp =>
        let (_, exp) := splitSign exp
        !exp.isEmpty && exp.all isDigit
      | _ => tail.isEmpty
    (!digits.isEmpty || !fraction.isEmpty) && validExponent

  readNumericText (t : Text) : Except AffinityError SqlValue := do
    unless t.encoding == .utf8 do throw (.unsupported .numericTextEncoding)
    let bytes := t.bytes.data.toList
    if bytes.contains 0 then throw (.unsupported .numericTextNul)
    let trimmed := ((bytes.dropWhile isSpace).reverse.dropWhile isSpace).reverse
    let (negative, unsigned) := splitSign trimmed
    let (digits, rest) := unsigned.span isDigit
    if !digits.isEmpty && rest.isEmpty then
      let limit : Nat := 2 ^ 63
      let magnitude := digits.foldl (fun n b => min (limit + 1) (10 * n + (b.toNat - 48))) 0
      if magnitude < limit || (negative && magnitude == limit) then
        let integer : Int := magnitude
        return .integer (Int64.ofInt (if negative then -integer else integer))
      throw (.unsupported .numericTextOverflow)
    if realSyntax digits rest then throw (.unsupported .numericTextRealSyntax)
    return .text t

  applyNumeric : SqlValue → Except AffinityError SqlValue
    | .text t => readNumericText t
    | .real r =>
      let f := Float.Model.ofBits r.bits
      let i := f.toInt64
      -- SQLite excludes the signed endpoints from REAL-to-INTEGER affinity.
      if i != Int64.minValue && i != Int64.maxValue && (Float.Model.ofInt64 i).beq f then
        .ok (.integer i)
      else .ok (.real r)
    | value => .ok value

/-- Apply affinity and any STRICT storage-class check. NULL passes this boundary. Row
constraints such as NOT NULL and INTEGER PRIMARY KEY are outside it. -/
def ColumnType.apply : ColumnType → SqlValue → Except AffinityError SqlValue
  | .ordinary affinity, value => affinity.apply value
  | .strict type, value =>
    match type.affinity.apply value with
    | .error error => .error error
    | .ok result =>
      if type.accepts result.storageClass then .ok result
      else .error (.datatype type result.storageClass)

end Silmaril.SQLite.Relational
