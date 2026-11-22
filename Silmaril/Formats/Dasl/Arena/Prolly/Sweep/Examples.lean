module

import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Thms
public meta import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Defs

namespace Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Examples

open Silmaril.Formats.Dasl.Prolly (route)

private def arena : Indexed Nat Nat String := ⟨#[
  .leaf [(1, "shared")], .leaf [(9, "unreachable")],
  .branch 1 [(1, .local 0), (3, .external 81)], .branch 1 [(1, .local 0), (4, .external 82)]]⟩

private def roots : List (Handle Nat) := [.local 2, .local 3, .external 9]
private def unavailable : Reader Nat Nat String := fun name => .error (.missing name)

#guard (sweep? arena roots [0, 2, 3, 4]).isNone
#guard (sweep? arena roots [0, 2]).isNone
#guard (sweep? arena roots [2, 3]).isNone

#guard match sweep? arena roots [0, 2, 3] with
  | none => false
  | some view =>
    decide (view.slots.size = 4) && view.slots[1]?.any Option.isNone && view.slots[4]?.isNone &&
      decide (view.read unavailable (.local 1) = .error (.missing (.local 1))) &&
      decide (route (view.read unavailable) 4 1 2 none (.local 2) = .ok (some "shared")) &&
      decide (route (view.read unavailable) 4 1 2 none (.local 3) = .ok (some "shared")) &&
      decide (route (view.read unavailable) 4 3 2 none (.local 2) = .error (.missing (.external 81))) &&
      decide (route (view.read unavailable) 4 1 2 none (.external 9) = .error (.missing (.external 9)))

end Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Examples
