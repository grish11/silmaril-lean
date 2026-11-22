module

import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Mark.Thms
public meta import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Mark.Defs
public meta import Silmaril.Formats.Dasl.Prolly.Route.Defs

namespace Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Mark.Examples

open Silmaril.Formats.Dasl.Prolly (route)

private def arena : Indexed Nat Nat String := ⟨#[
  .leaf [(1, "shared")], .leaf [(2, "dead")],
  .branch 1 [(1, .local 0), (3, .external 90)], .branch 1 [(1, .local 0)],
  .leaf [(5, "separate")]]⟩

private def directory : Nat → Option (Handle Nat)
  | 5 => some (.local 2)
  | 6 => some (.local 3)
  | 7 => some (.local 4)
  | _ => none

private def missing : Reader Nat Nat String := fun name => .error (.missing name)

#guard match markAndSweep? arena (directoryRoots directory [5, 6, 7]) with
  | none => false
  | some view => decide (view.slots.size = 5 ∧ view.slots[1]? = some none ∧
      view.slots[0]? = some (some (.leaf [(1, "shared")])) ∧
      route (view.read missing) 3 1 2 none (.local 2) = route (arena.read missing) 3 1 2 none (.local 2))

#guard match markAndSweep? arena (directoryRoots directory [5, 6]) with
  | none => false
  | some view => decide (view.slots[4]? = some none ∧ view.slots[5]? = none ∧
      route (view.read missing) 3 3 2 none (.local 2) = .error (.missing (.external 90)) ∧
      route (view.read missing) 3 1 2 none (.local 3) = .ok (some "shared"))

#guard (markAndSweep? arena [.local 17]).isNone
#guard (markAndSweep? (⟨#[.branch 1 [(1, .local 17)]]⟩ : Indexed Nat Nat String) [.local 0]).isNone

end Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Mark.Examples
