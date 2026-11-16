module

public import Silmaril.Formats.JsonWire.Parser.Defs

/-!
# JSON on the wire: the grammar the reader implements, over tokens

The RFC 8259 reader `Silmaril.Formats.JsonWire.parse?` is a lexer (`Internal.lex`) followed by a
fuel-bounded recursive-descent parser (`Internal.value?`). This module states what each stage
computes declaratively, so that the reader can be compared with a grammar one stage at a time:

* `TValue`, `TElems`, `TElemsNE`, `TMembers`, `TMembersNE`: the RFC 8259 value grammar (§2–§5) over
  the lexer's tokens. A list of tokens is a `TValue` when it is one value, brackets and
  separators included. They mirror the parser's procedures (`value?`, `array?`, `object?`, with
  `allowEmpty` true for the first element), so that the parser is proved sound and complete
  for them by induction (`Silmaril.Formats.JsonWire.Grammar.Thms`).
* `tokensOf cs`: the tokens of `cs` under `lex .rfc8259`, with enough fuel.

The scalar tokens include the identifiers `null`, `true`, `false`, `Infinity` and `NaN`, because
the parser accepts them in every dialect. The RFC 8259 lexer never produces identifiers.
-/

@[expose] public section

namespace Silmaril.Formats.JsonWire.Internal

/-- The tokens the parser reads as a scalar value. -/
def Token.IsScalar : Token → Prop
  | .null | .bool _ | .string _ | .number _ => True
  | .identifier name true => name = stringUnits "null" ∨ name = stringUnits "true" ∨
      name = stringUnits "false" ∨ name = stringUnits "Infinity" ∨ name = stringUnits "NaN"
  | _ => False

mutual
/-- `value`: a scalar, or an array or object with its brackets. -/
inductive TValue : List Token → Prop
  | scalar {t : Token} : t.IsScalar → TValue [t]
  | array {xs : List Token} : TElems xs → TValue (.arrayOpen :: xs)
  | object {xs : List Token} : TMembers xs → TValue (.objectOpen :: xs)
/-- What follows `[`: `]`, or elements and `]`. -/
inductive TElems : List Token → Prop
  | empty : TElems [.arrayClose]
  | ne {xs : List Token} : TElemsNE xs → TElems xs
/-- `value *( value-separator value ) end-array`. -/
inductive TElemsNE : List Token → Prop
  | last {v : List Token} : TValue v → TElemsNE (v ++ [.arrayClose])
  | cons {v xs : List Token} : TValue v → TElemsNE xs → TElemsNE (v ++ .comma :: xs)
/-- What follows `{`: `}`, or members and `}`. -/
inductive TMembers : List Token → Prop
  | empty : TMembers [.objectClose]
  | ne {xs : List Token} : TMembersNE xs → TMembers xs
/-- `member *( value-separator member ) end-object`, with `member = string name-separator value`. -/
inductive TMembersNE : List Token → Prop
  | last {k : Units} {v : List Token} : TValue v →
      TMembersNE (.string k :: .colon :: (v ++ [.objectClose]))
  | cons {k : Units} {v xs : List Token} : TValue v → TMembersNE xs →
      TMembersNE (.string k :: .colon :: (v ++ .comma :: xs))
end

/-- A hexadecimal digit, either case. -/
def IsHexChar (c : Char) : Prop :=
  (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 102) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 70)

/-- The characters of an RFC 8259 string between its quotation marks (§7): unescaped characters
(not a control character, `"` or `\`), the two-character escapes and `\uXXXX`. -/
inductive StrBody : List Char → Prop
  | nil : StrBody []
  | plain {c : Char} {b : List Char} : 0x20 ≤ c.toNat → c ≠ '"' → c ≠ '\\' → StrBody b →
      StrBody (c :: b)
  | escape {e : Char} {b : List Char} : e ∈ ['"', '\\', '/', 'b', 'f', 'n', 'r', 't'] →
      StrBody b → StrBody ('\\' :: e :: b)
  | unit {h₁ h₂ h₃ h₄ : Char} {b : List Char} : IsHexChar h₁ → IsHexChar h₂ → IsHexChar h₃ →
      IsHexChar h₄ → StrBody b → StrBody ('\\' :: 'u' :: h₁ :: h₂ :: h₃ :: h₄ :: b)

/-- A decimal digit `0`–`9`. -/
def IsDigitChar (c : Char) : Prop := 48 ≤ c.toNat ∧ c.toNat ≤ 57

/-- `1*DIGIT`. -/
def Digits (ds : List Char) : Prop := ds ≠ [] ∧ ∀ x ∈ ds, IsDigitChar x

/-- An RFC 8259 number (§6): `[ minus ] int [ frac ] [ exp ]`, with `int = zero / ( digit1-9 *DIGIT )`,
`frac = "." 1*DIGIT` and `exp = ( "e" / "E" ) [ "-" / "+" ] 1*DIGIT`. -/
def NumberChars (w : List Char) : Prop :=
  ∃ s i f e, w = s ++ i ++ f ++ e ∧ (s = [] ∨ s = ['-']) ∧
    (i = ['0'] ∨ ∃ d ds, i = d :: ds ∧ 49 ≤ d.toNat ∧ d.toNat ≤ 57 ∧ ∀ x ∈ ds, IsDigitChar x) ∧
    (f = [] ∨ ∃ ds, f = '.' :: ds ∧ Digits ds) ∧
    (e = [] ∨ ∃ x sg ds, e = x :: (sg ++ ds) ∧ (x = 'e' ∨ x = 'E') ∧
      (sg = [] ∨ sg = ['-'] ∨ sg = ['+']) ∧ Digits ds)

/-- The characters of one token (`Lexeme l t`): what the RFC 8259 lexer reads as `t`. A string or
number lexeme stands for any token of its kind (any code units, any finite decimal): the lexeme fixes
the kind, not the value. -/
inductive Lexeme : List Char → Token → Prop
  | arrayOpen : Lexeme ['['] .arrayOpen
  | arrayClose : Lexeme [']'] .arrayClose
  | objectOpen : Lexeme ['{'] .objectOpen
  | objectClose : Lexeme ['}'] .objectClose
  | comma : Lexeme [','] .comma
  | colon : Lexeme [':'] .colon
  | string {b : List Char} {u : Units} : StrBody b → Lexeme ('"' :: (b ++ ['"'])) (.string u)
  | number {w : List Char} {d : Decimal} : NumberChars w → Lexeme w (.number (.finite d))
  | true_ : Lexeme "true".toList (.bool true)
  | false_ : Lexeme "false".toList (.bool false)
  | null : Lexeme "null".toList .null

/-- `cs` is whitespace and the lexemes of `ts`, in order (`Lexes cs ts`). -/
inductive Lexes : List Char → List Token → Prop
  | nil : Lexes [] []
  | white {c : Char} {cs : List Char} {ts : List Token} : white .rfc8259 c = true → Lexes cs ts →
      Lexes (c :: cs) ts
  | token {l cs : List Char} {t : Token} {ts : List Token} : Lexeme l t → Lexes cs ts →
      Lexes (l ++ cs) (t :: ts)

/-- The tokens of `cs` under the RFC 8259 lexer, given enough fuel (one per character). -/
def tokensOf (cs : List Char) : Option (List Token) :=
  (lex .rfc8259 (cs.length + 1) 0 cs).map Lexed.tokens

end Silmaril.Formats.JsonWire.Internal

end
