module

public import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Mark.Defs
public import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Thms
import Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Mark

public section

namespace Silmaril.Formats.Dasl.Arena.Prolly.Sweep

open Silmaril.Formats.Dasl.Prolly (route)

variable {Name Key Payload : Type} {arena : Indexed Name Key Payload}
variable {view : Collected Name Key Payload} {roots : List (Handle Name)}

theorem mark_checked (ready : Markable arena roots) : check arena roots (mark arena roots) = true :=
  Proofs.Formats.Dasl.Arena.Prolly.Mark.checked ready

theorem markAndSweep_exists (ready : Markable arena roots) : ∃ view, markAndSweep? arena roots = some view := by
  simp [markAndSweep?, sweep?, mark_checked ready]

/-- The computed certificate marks exactly the reachable local indices if
accepted. Backwardness and liveness suffice for acceptance, but are not
additional assumptions for soundness of a successful sweep. -/
theorem mark_exact {index : Nat} (swept : markAndSweep? arena roots = some view) :
    index ∈ mark arena roots ↔ Reachable arena roots (.local index) :=
  Proofs.Formats.Dasl.Arena.Prolly.Mark.exact_of_swept swept

theorem marked_slot (swept : markAndSweep? arena roots = some view) (index : Nat)
    (live : index < arena.blocks.size) :
    (view.slots[index]? = some (some arena.blocks[index]) ↔ Reachable arena roots (.local index)) ∧
    (view.slots[index]? = some none ↔ ¬ Reachable arena roots (.local index)) :=
  Proofs.Formats.Dasl.Arena.Prolly.Mark.collected_slot swept index live

theorem route_marked [LinearOrder Key] (swept : markAndSweep? arena roots = some view)
    (external : Reader Name Key Payload) (width fuel : Nat) (key : Key)
    {expected : Option Nat} {ref : Handle Name} (reachable : Reachable arena roots ref) :
    route (view.read external) width key fuel expected ref = route (arena.read external) width key fuel expected ref :=
  route_reachable swept external width fuel key reachable

theorem route_selected [LinearOrder Key] {Outer : Type}
    {directory : Outer → Option (Handle Name)} {keys : List Outer} {selected : Outer} {ref : Handle Name}
    (swept : markAndSweep? arena (directoryRoots directory keys) = some view)
    (member : selected ∈ keys) (found : directory selected = some ref)
    (external : Reader Name Key Payload) (width fuel : Nat) (key : Key) :
    route (view.read external) width key fuel none ref = route (arena.read external) width key fuel none ref :=
  route_marked swept external width fuel key (.root (List.mem_filterMap.mpr ⟨selected, member, found⟩))

theorem route_directory [LinearOrder Key] {Outer : Type}
    {directory : Outer → Option (Handle Name)} {keys : List Outer} {selected : Outer} {ref : Handle Name}
    (swept : markAndSweep? arena (directoryRoots directory keys) = some view)
    (covers : CoversDirectory directory keys) (found : directory selected = some ref)
    (external : Reader Name Key Payload) (width fuel : Nat) (key : Key) :
    route (view.read external) width key fuel none ref = route (arena.read external) width key fuel none ref :=
  route_selected swept (covers selected (by simp [found])) found external width fuel key

end Silmaril.Formats.Dasl.Arena.Prolly.Sweep
