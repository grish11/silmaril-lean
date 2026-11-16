module

public import Mathlib.Computability.Language
public import Silmaril.Formats.Bytes

/-!
# SPKI S-expressions in canonical form (RFC 9804)

RFC 9804 ("Simple Public Key Infrastructure (SPKI) S-Expressions", Rivest and Eastlake, 2025;
the published form of draft-rivest-sexp) fixes a data model and several representations. This
module defines the data model and the **canonical representation** (§6.2, ABNF §7.2), the one
used for signing:

```
c-sexp   = c-string / ( "(" *c-sexp ")" )
c-string = [ "[" verbatim "]" ] verbatim
verbatim = decimal ":" *OCTET    ; exactly `decimal` octets
decimal  = %x30 / ( %x31-39 *DIGIT )
```

* `Sexp`: an octet string with an optional display hint (§4.6; hints do not nest), or a list.
* `decimal n`: the decimal digits of `n`, with no leading zero. `IsDecimal ds` transcribes the
  `decimal` rule; `decimal` is exactly the strings it allows (`isDecimal_iff`).
* `encode`: the canonical representation. `canonical`, its image, is the language of §7.2:
  `ABNF` transcribes the ABNF rule for rule and `mem_canonical_iff` proves they agree.
* RFC 9804 §6.2 says the canonical form "is uniquely defined for each S-expression". Here that is
  a theorem: `encode` is injective (`encode_injective`), because `parse` inverts it
  (`parse_encode`) and accepts nothing else (`eq_encode_of_parse`).

The transport representations (§6.3: base-64 of the canonical form in braces) and the advanced
representation (§6.4, §7.1: tokens, quoted strings, hexadecimal, base-64, whitespace) are not
defined here. `Silmaril.Formats.RivestSExp.parseCanonical?` is an older reader of the canonical
form without display hints; no theorem relates it to this language.

References (`references.bib`): `rfc9804` (§4.6, §6.2, §7.2).
Lemmas: `Silmaril.Formats.Spki.Thms`.
-/

@[expose] public section

namespace Silmaril.Formats.Spki

/-! ## Data model and canonical encoding -/

/-- An S-expression: an octet string with an optional display hint, or a list. -/
inductive Sexp where
  /-- An octet string, with an optional display hint (itself an octet string). -/
  | atom (hint : Option (List UInt8)) (octets : List UInt8)
  /-- A list of S-expressions. -/
  | list (items : List Sexp)
  deriving Repr

mutual

/-- Decidable equality of S-expressions. -/
def Sexp.decEq : (x y : Sexp) → Decidable (x = y)
  | .atom h s, .atom h' s' =>
    if hh : h = h' then
      if hs : s = s' then isTrue (by rw [hh, hs])
      else isFalse (by intro e; cases e; exact hs rfl)
    else isFalse (by intro e; cases e; exact hh rfl)
  | .atom _ _, .list _ => isFalse (by intro e; cases e)
  | .list _, .atom _ _ => isFalse (by intro e; cases e)
  | .list xs, .list ys =>
    match Sexp.decEqList xs ys with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)

/-- Decidable equality of lists of S-expressions. -/
def Sexp.decEqList : (xs ys : List Sexp) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
  | x :: xs, y :: ys =>
    match Sexp.decEq x y, Sexp.decEqList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h₁, _ => isFalse (by intro e; cases e; exact h₁ rfl)
    | _, isFalse h₂ => isFalse (by intro e; cases e; exact h₂ rfl)

end

instance : DecidableEq Sexp := Sexp.decEq

/-- An ASCII decimal digit `0..9`. -/
def isDigit (b : UInt8) : Bool := 0x30 ≤ b && b ≤ 0x39

/-- The value of a string of decimal digits. -/
def digitsValue (ds : List UInt8) : Nat := ds.foldl (fun n d => 10 * n + (d.toNat - 0x30)) 0

/-- The `decimal` rule: `0`, or a non-zero digit followed by digits. -/
def IsDecimal (ds : List UInt8) : Prop :=
  ds = [0x30] ∨ ∃ d t, ds = d :: t ∧ 0x31 ≤ d ∧ d ≤ 0x39 ∧ ∀ b ∈ t, isDigit b = true

/-- The decimal digits of `n`, most significant first, without leading zeros. -/
def decimal (n : Nat) : List UInt8 :=
  if n < 10 then [UInt8.ofNat (0x30 + n)] else decimal (n / 10) ++ [UInt8.ofNat (0x30 + n % 10)]

/-- `verbatim`: the length in decimal, a colon, the octets. -/
def verbatim (s : List UInt8) : List UInt8 := decimal s.length ++ 0x3A :: s

mutual

/-- The canonical representation (RFC 9804 §6.2). -/
def encode : Sexp → List UInt8
  | .atom none s => verbatim s
  | .atom (some h) s => 0x5B :: verbatim h ++ 0x5D :: verbatim s
  | .list xs => 0x28 :: encodeList xs ++ [0x29]

/-- The canonical representations of the items of a list, concatenated. -/
def encodeList : List Sexp → List UInt8
  | [] => []
  | x :: xs => encode x ++ encodeList xs

end

/-- The language of canonical S-expressions. -/
def canonical : Language UInt8 := Set.range encode

/-! ## The ABNF of §7.2, transcribed -/

/-- `verbatim = decimal ":" *OCTET`, with exactly `decimal` octets. -/
def IsVerbatim (w : List UInt8) : Prop :=
  ∃ ds s, IsDecimal ds ∧ digitsValue ds = s.length ∧ w = ds ++ 0x3A :: s

/-- `c-string = [ "[" verbatim "]" ] verbatim`. -/
def IsCString (w : List UInt8) : Prop :=
  IsVerbatim w ∨ ∃ h v, IsVerbatim h ∧ IsVerbatim v ∧ w = 0x5B :: h ++ 0x5D :: v

/-- `c-sexp = c-string / ( "(" *c-sexp ")" )`. -/
inductive ABNF : List UInt8 → Prop
  | string {w} : IsCString w → ABNF w
  | list {xs : List (List UInt8)} : (∀ x ∈ xs, ABNF x) → ABNF (0x28 :: xs.flatten ++ [0x29])

/-! ## A parser -/

/-- Read `decimal ":"`; the digits must be the canonical decimal of their value. -/
def readDecimal (w : List UInt8) : Option (Nat × List UInt8) :=
  match w.dropWhile isDigit with
  | b :: r =>
    if b = 0x3A ∧ decimal (digitsValue (w.takeWhile isDigit)) = w.takeWhile isDigit then
      some (digitsValue (w.takeWhile isDigit), r)
    else none
  | [] => none

/-- Read a `verbatim`: its octets and the rest of the input. -/
def readVerbatim (w : List UInt8) : Option (List UInt8 × List UInt8) :=
  match readDecimal w with
  | some (n, r) => if n ≤ r.length then some (r.take n, r.drop n) else none
  | none => none

/-- Read `"[" verbatim "]" verbatim` after the `[`. -/
def readHinted (w : List UInt8) : Option (Sexp × List UInt8) :=
  match readVerbatim w with
  | some (h, b :: r) =>
    if b = 0x5D then (readVerbatim r).map fun (s, r') => (.atom (some h) s, r') else none
  | _ => none

mutual

/-- Read one canonical S-expression from the front of the input, with fuel. -/
def parse : Nat → List UInt8 → Option (Sexp × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, b :: r =>
    if b = 0x28 then (parseList n r).map fun (xs, r') => (.list xs, r')
    else if b = 0x5B then readHinted r
    else (readVerbatim (b :: r)).map fun (s, r') => (.atom none s, r')

/-- Read list items up to and including `)`, with fuel. -/
def parseList : Nat → List UInt8 → Option (List Sexp × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, b :: r =>
    if b = 0x29 then some ([], r)
    else match parse n (b :: r) with
      | some (x, r') => (parseList n r').map fun (xs, r'') => (x :: xs, r'')
      | none => none

end

/-- Decode a whole input as one canonical S-expression. -/
def decode (w : List UInt8) : Option Sexp :=
  match parse (w.length + 1) w with
  | some (x, []) => some x
  | _ => none

end Silmaril.Formats.Spki

end
