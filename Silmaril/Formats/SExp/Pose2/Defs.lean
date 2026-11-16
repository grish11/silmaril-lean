module

public import Silmaril.Formats.SExp.Printer

/-!
# Portable S-expressions (POSE) as `SExp2`

POSE ("Portable S-Expressions", the `s-expressions/pose` specification implemented by
`Silmaril.Formats.Pose`) is a deliberately small common subset of Lisp syntaxes: proper lists,
lowercase ASCII symbols, strings with only `\\` and `\"` escapes, and JSON-style numbers. It has
**no dotted-pair notation**, so `Pose2 := SExp2 PoseAtom` is the dotted view of POSE data:

* `Pose2.parse?` reads POSE text (via `Pose.parse?`) and embeds it with `SExp.toSExp2`, so every
  result is recursively proper (`Thms.isProper_of_parse?`) and `(a . b)` is rejected;
* `Pose2.toPose?` is the computable partial inverse on proper data, and `Pose2.print?` writes a
  proper `Pose2` value whose atoms satisfy the POSE grammar; improper values have no POSE text
  (`Thms.print?_eq_none_of_not_proper`).

New definitions (no source; POSE grammar as in `Silmaril.Formats.SExp.Pose`).
-/

@[expose] public section

namespace Silmaril.Formats

/-- POSE data viewed as dotted S-expressions. -/
abbrev Pose2 := SExp2 PoseAtom

namespace Pose2

/-- The embedding of POSE data. -/
def ofPose (p : Pose) : Pose2 := p.toSExp2

/-- Number of nodes. -/
def size : Pose2 → Nat
  | .nil | .atom _ => 1
  | .cons a d => size a + size d + 1

/-- The proper part, computably (`SExpParser.toProper` with enough fuel). -/
def toPose? (e : Pose2) : Option Pose := SExpParser.toProper (size e + 1) e

/-- Read exactly one POSE datum. -/
def parse? (s : String) : Option Pose2 := ofPose <$> Pose.parse? s

/-- Read a POSE document. -/
def parseDocument? (s : String) : Option (List Pose2) := (·.map ofPose) <$> Pose.parseDocument? s

/-- Print a proper value whose atoms satisfy the POSE grammar. -/
def print? (e : Pose2) : Option String := e.toPose?.bind Pose.print?

end Pose2

end Silmaril.Formats
