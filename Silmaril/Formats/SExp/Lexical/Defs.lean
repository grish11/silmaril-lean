module

public import Silmaril.Formats.SExp.Reader.Defs
public import Mathlib.Data.Rat.Defs

/-!
# Lexical building blocks shared by the Lisp-family readers

Character-level scanners over `List Char`, each paired (in `Thms`) with the printer it inverts:

* `takeToken p`: the longest prefix of characters satisfying `p` (a bare token up to the next
  delimiter);
* `readQuoted q esc`: the body of a literal delimited by `q` with backslash escapes decoded by
  `esc` (strings `"…"`, `|…|` symbols), inverted by `escapeQuoted q`, which escapes only `q` and
  the backslash;
* `digits?`, `int?`, `rational?`: decimal naturals, integers and exact rationals (`n/d`),
  inverted by `natText`, `intText`, `ratText`;
* `readDecimal`: decimal floating literals (`[sign] digits [. digits] [marker [sign] digits]`),
  read as the exact `Decimal` they denote (sign, significand, power of ten), inverted by
  `Decimal.text`. No binary rounding is applied: two literals with the same decimal value but
  different digits (`1.5`, `1.50`) give different `Decimal`s with the same `Decimal.value`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Formats.SExpLexical

/-- The longest prefix whose characters satisfy `p`, and the rest. -/
def takeToken (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: r =>
      if p c then
        let (w, rest) := takeToken p r
        (c :: w, rest)
      else ([], c :: r)

mutual
  /-- Read the body of a literal up to the unescaped closer `q`, decoding `\c` by `esc c`. -/
  def readQuoted (q : Char) (esc : Char → Option Char) :
      List Char → Option (List Char × List Char)
    | [] => none
    | c :: r =>
        if c = q then some ([], r)
        else if c = '\\' then readEscape q esc r
        else (readQuoted q esc r).map fun (w, rest) => (c :: w, rest)

  /-- The character after a backslash. -/
  def readEscape (q : Char) (esc : Char → Option Char) :
      List Char → Option (List Char × List Char)
    | [] => none
    | e :: r =>
        match esc e with
        | some d => (readQuoted q esc r).map fun (w, rest) => (d :: w, rest)
        | none => none
end

/-- Escape exactly the closer `q` and the backslash. -/
def escapeQuoted (q : Char) : List Char → List Char
  | [] => []
  | c :: r => (if c = q || c = '\\' then ['\\', c] else [c]) ++ escapeQuoted q r

/-- Escape the closer `q` and the backslash, and write newline, return and tab as `\n`, `\r`,
`\t` (the escapes of `SExpPrinter.escapeChar`); every other character is written as itself. -/
def escapeMnemonic (q : Char) : List Char → List Char
  | [] => []
  | c :: r =>
      (if c = q || c = '\\' then ['\\', c]
       else if c = '\n' then ['\\', 'n'] else if c = '\r' then ['\\', 'r']
       else if c = '\t' then ['\\', 't'] else [c]) ++ escapeMnemonic q r

/-! ## Numerals -/

def natText (n : Nat) : List Char := Nat.toDigits 10 n

def intText (n : Int) : List Char :=
  if n < 0 then '-' :: natText n.natAbs else natText n.toNat

/-- The value of decimal digits (`Nat.ofDigitChars 10 · 0`, as an exposed fold so that the
kernel can evaluate examples). -/
def ofDigits (cs : List Char) : Nat :=
  cs.foldl (fun acc c => 10 * acc + (c.toNat - '0'.toNat)) 0

/-- A nonempty string of decimal digits. -/
def digits? (cs : List Char) : Option Nat :=
  if cs ≠ [] ∧ cs.all Char.isDigit = true then some (ofDigits cs) else none

/-- An optionally signed decimal integer. -/
def int? : List Char → Option Int
  | [] => none
  | c :: r =>
      if c = '-' then (fun n : Nat => -(n : Int)) <$> digits? r
      else if c = '+' then (fun n : Nat => (n : Int)) <$> digits? r
      else (fun n : Nat => (n : Int)) <$> digits? (c :: r)

/-- An exact rational: an integer, or `integer/natural` with nonzero denominator. -/
def rational? (cs : List Char) : Option ℚ :=
  match takeToken (fun c => c != '/') cs with
  | (num, []) => (fun n : Int => (n : ℚ)) <$> int? num
  | (num, _ :: den) =>
      match int? num, digits? den with
      | some n, some d => if d = 0 then none else some ((n : ℚ) / d)
      | _, _ => none

/-- The canonical text of a rational: `n` or `n/d` in lowest terms. -/
def ratText (q : ℚ) : List Char :=
  if q.den = 1 then intText q.num else intText q.num ++ '/' :: natText q.den

/-! ## Decimal floating literals -/

/-- The exact value written by a decimal floating literal: `± significand × 10 ^ exponent`.
The sign is kept separately so that `-0.0` is distinct from `0.0`. -/
structure Decimal where
  negative : Bool
  significand : Nat
  exponent : Int
  deriving DecidableEq, Repr

namespace Decimal

/-- The exact rational value (the sign of zero is lost). -/
def value (d : Decimal) : ℚ :=
  (if d.negative then -1 else 1) * (d.significand : ℚ) *
    (if 0 ≤ d.exponent then ((10 : ℚ) ^ d.exponent.toNat) else ((10 : ℚ) ^ (-d.exponent).toNat)⁻¹)

/-- Text with an exponent marker: `[-]significand marker exponent`, e.g. `-15e-1`. -/
def text (marker : Char) (d : Decimal) : List Char :=
  (if d.negative then ['-'] else []) ++ natText d.significand ++ marker :: intText d.exponent

end Decimal

/-- An optional leading sign. -/
def sign : List Char → Bool × List Char
  | [] => (false, [])
  | c :: r => if c = '-' then (true, r) else if c = '+' then (false, r) else (false, c :: r)

/-- Read a decimal floating literal `[sign] digits [. digits] [marker [sign] digits]` with at least
one digit and either a point or an exponent; returns the exponent marker used, if any. -/
def readDecimal (isMarker : Char → Bool) (cs : List Char) : Option (Decimal × Option Char) :=
  let (neg, body) := sign cs
  let (whole, r₁) := takeToken Char.isDigit body
  let (frac, point, r₂) : List Char × Bool × List Char :=
    match r₁ with
    | c :: r =>
        if c = '.' then
          let (f, r') := takeToken Char.isDigit r
          (f, true, r')
        else ([], false, c :: r)
    | [] => ([], false, [])
  if whole.isEmpty && frac.isEmpty then none
  else
    let sig := ofDigits (whole ++ frac)
    match r₂ with
    | [] => if point then some (⟨neg, sig, -(frac.length : Int)⟩, none) else none
    | m :: r₃ =>
        if isMarker m then
          (fun e : Int => (⟨neg, sig, e - frac.length⟩, some m)) <$> int? r₃
        else none

end Silmaril.Formats.SExpLexical
