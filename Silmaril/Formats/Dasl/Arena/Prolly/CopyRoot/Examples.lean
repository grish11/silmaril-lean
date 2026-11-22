module

import Silmaril.Formats.Dasl.Arena.Prolly.CopyRoot.Thms
public meta import Silmaril.Formats.Dasl.Arena.Prolly.CopyRoot.Defs

namespace Silmaril.Formats.Dasl.Arena.Prolly.CopyRoot.Examples

private def before : Directory String Nat Nat String :=
  ⟨⟨#[.leaf [(1, "old")]]⟩, fun root => if root = "first" ∨ root = "alias" then some (.local 0) else none⟩

private def unavailable : Reader Nat Nat String := fun name => .error (.missing name)

#guard (before.copy? "first" (.branch 1 [(1, .local 1)])).isNone

#guard match before.copy? "first" (.leaf [(1, "new")]) with
  | none => false
  | some (after, index) =>
    decide (index = 1 ∧ after.roots "first" = some (.local 1) ∧ after.roots "alias" = some (.local 0)) &&
      decide (after.roots "unused" = none) &&
      decide (after.arena.lookup unavailable 4 1 index 1 = .ok (some "new")) &&
      decide (after.arena.lookup unavailable 4 1 0 1 = .ok (some "old"))

end Silmaril.Formats.Dasl.Arena.Prolly.CopyRoot.Examples
