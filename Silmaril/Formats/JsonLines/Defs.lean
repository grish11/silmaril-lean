module

public import Silmaril.Formats.JsonBytes.Depth.Defs

/-!
# JSON Lines over bytes

A JSON Lines file is a sequence of JSON texts, one per line. This module defines the byte
languages of such files for an explicit `Policy`, over any language of line contents. It
also fixes the JSON instances: `JsonLines.language pol p` (each line a JSON text of
`JsonBytes.language p`) and `JsonLines.languageAt pol p d` (each line of nesting depth at most
`d`).

## Sources and the policy choices

There are two informal specifications, and they differ. Neither is an RFC.

* **JSON Lines** (jsonlines.org, `jsonlines`): UTF-8, no byte-order mark. "Each line is a
  valid JSON value", so "a blank line is not" a line. The line terminator is `\n` (`0A`).
  `\r\n` "is also supported because surrounding white space is implicitly ignored", so a
  `0D` before `0A` is trailing JSON whitespace. A terminator after the last value is "strongly
  recommended but not required", and if present it "must be the last byte in the file".
  This is `Policy.jsonLines`.
* **NDJSON** (the ndjson-spec README, `ndjson-spec`): every JSON text "MUST be … followed by
  the newline character `\n`", which "MAY be preceded by a carriage return `\r`". The texts
  "MUST NOT contain newlines or carriage returns". A parser "MAY silently ignore empty lines",
  configurably. `Policy.ndjson` is the writer side: final newline required, no blank lines,
  no `0D` inside a text, at most one `0D` just before each `0A`. A parser that skips blank
  lines accepts `{ Policy.ndjson with blankLines := true }`.

The fields of `Policy` make each choice explicit:

* `final`: whether the last line is followed by `0A` (`required`, `optional`, `forbidden`);
* `blankLines`: whether a line may be empty. With `final := .optional` and blank lines
  allowed, `1\n` is both one terminated line and one line followed by an empty line, so the
  item list is not determined by the bytes; the language is unaffected;
* `crInText`: whether `0D` may occur inside a line's text (as JSON whitespace, as in
  JSON Lines) or only as one byte just before `0A` (as in NDJSON).

A line never contains `0A`. JSON allows `0A` as whitespace between tokens, so a JSON text that
spans several lines is valid JSON but not a JSON Lines line.

The empty file (zero lines) is in the language under every policy. Neither source addresses
it; it is the empty sequence of values. Encoding is UTF-8 because every line is (each JSON text
is UTF-8, `JsonBytes.language_isWellFormed`); a byte-order mark is excluded because no JSON text
starts with one.

## Bounds

Bounds are bounds on the line language, so they compose with the framing: per-line nesting
depth is `languageAt`, and per-line length is `frameLang pol (L ⊓ {w | w.length ≤ n})`. The
whole-file length is `Silmaril.Accept.upTo List.length n`. With a required final newline the
framing is `Silmaril.Streams.frameItems 0A` (`Thms`), so the generic per-item bound
`Silmaril.Streams.ItemBound` applies.

References (`references.bib`): `jsonlines`, `ndjson-spec`, `rfc8259`.
-/

@[expose] public section

namespace Silmaril.Formats.JsonLines

/-- The line feed `0A`, the line terminator. -/
def lf : UInt8 := 0x0A

/-- The carriage return `0D`. -/
def cr : UInt8 := 0x0D

/-- Whether the last line is followed by a line feed. -/
inductive FinalNewline where
  | required
  | optional
  | forbidden
  deriving DecidableEq, Repr

/-- The framing choices of a line-delimited JSON dialect. -/
structure Policy where
  /-- Whether the last line is terminated. -/
  final : FinalNewline
  /-- Whether empty lines are allowed. -/
  blankLines : Bool
  /-- Whether `0D` may occur inside a line's text (otherwise only just before `0A`). -/
  crInText : Bool
  deriving DecidableEq, Repr

/-- jsonlines.org. -/
def Policy.jsonLines : Policy := ⟨.optional, false, true⟩

/-- The NDJSON writer rules. -/
def Policy.ndjson : Policy := ⟨.required, false, false⟩

/-- The text of one line over a content language `L`. With `crInText`, any member of `L`
without `0A`; otherwise a member of `L` without `0A` or `0D`, optionally followed by one `0D`. -/
def textLine (crInText : Bool) (L : Language UInt8) : Language UInt8 :=
  {w | (crInText = true ∧ lf ∉ w ∧ w ∈ L) ∨
    (crInText = false ∧ ∃ t, (w = t ∨ w = t ++ [cr]) ∧ lf ∉ t ∧ cr ∉ t ∧ t ∈ L)}

/-- The lines a policy allows over a content language `L`. -/
def lineOf (pol : Policy) (L : Language UInt8) : Language UInt8 :=
  {w | (w = [] ∧ pol.blankLines = true) ∨ w ∈ textLine pol.crInText L}

/-- Lines joined by `0A`, the last one unterminated. -/
def joined (lines : List (List UInt8)) : List UInt8 := [lf].intercalate lines

/-- Lines each terminated by `0A`. -/
def terminated (lines : List (List UInt8)) : List UInt8 := [lf].intercalate (lines ++ [[]])

/-- The files a final-newline choice allows for a list of lines. -/
def Framed : FinalNewline → List (List UInt8) → List UInt8 → Prop
  | .required, lines, w => w = terminated lines
  | .forbidden, lines, w => w = joined lines
  | .optional, lines, w => w = terminated lines ∨ w = joined lines

/-- The files whose lines are allowed lines over `L`. -/
def frameLang (pol : Policy) (L : Language UInt8) : Language UInt8 :=
  {w | ∃ lines : List (List UInt8), (∀ l ∈ lines, l ∈ lineOf pol L) ∧ Framed pol.final lines w}

/-- JSON Lines files whose lines are JSON texts of `JsonBytes.language p`. -/
def language (pol : Policy) (p : JsonBytes.Profile) : Language UInt8 :=
  frameLang pol (JsonBytes.language p)

/-- JSON Lines files each of whose lines has nesting depth at most `d`. -/
def languageAt (pol : Policy) (p : JsonBytes.Profile) (d : Nat) : Language UInt8 :=
  frameLang pol (JsonBytes.languageAt p d)

/-! ## A decision procedure, given one for the line contents -/

/-- `textLine`, given a check `ok` for the content language. -/
def textLineB (crInText : Bool) (ok : List UInt8 → Bool) (w : List UInt8) : Bool :=
  if crInText then !w.contains lf && ok w
  else
    let t := if w.getLast? = some cr then w.dropLast else w
    !t.contains lf && !t.contains cr && ok t

/-- `lineOf`, given a check for the content language. -/
def lineOfB (pol : Policy) (ok : List UInt8 → Bool) (w : List UInt8) : Bool :=
  (w.isEmpty && pol.blankLines) || textLineB pol.crInText ok w

/-- `List.splitOn lf`, by structural recursion (so the kernel evaluates it; `Thms`:
`splitLf_eq`). -/
def splitLf : List UInt8 → List (List UInt8)
  | [] => [[]]
  | b :: w => if b == lf then [] :: splitLf w else (splitLf w).modifyHead (b :: ·)

/-- `frameLang`, given a check for the content language: split the input at every `0A`. -/
def frameB (pol : Policy) (ok : List UInt8 → Bool) (w : List UInt8) : Bool :=
  let ls := splitLf w
  let req := decide (ls.getLast? = some []) && ls.dropLast.all (lineOfB pol ok)
  let forb := w.isEmpty || ls.all (lineOfB pol ok)
  match pol.final with
  | .required => req
  | .forbidden => forb
  | .optional => req || forb

end Silmaril.Formats.JsonLines

end
