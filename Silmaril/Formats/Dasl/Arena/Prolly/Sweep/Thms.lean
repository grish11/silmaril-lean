module

public import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Defs
import Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Sweep

public section

namespace Silmaril.Formats.Dasl.Arena.Prolly.Sweep

open Silmaril.Formats.Dasl.Prolly (route)

variable {Name Key Payload : Type} {arena : Indexed Name Key Payload}
variable {view : Collected Name Key Payload} {roots : List (Handle Name)} {indices : List Nat}

theorem sweep_spec (swept : sweep? arena roots indices = some view) :
    check arena roots indices = true ∧ view.slots.size = arena.blocks.size ∧
      ∀ index : Nat, view.slots[index]? =
        (arena.blocks[index]?).map (fun block => if indices.contains index then some block else none) :=
  Proofs.Formats.Dasl.Arena.Prolly.Sweep.sweep_spec swept

theorem keep_reachable (checked : check arena roots indices = true)
    {ref : Handle Name} (reachable : Reachable arena roots ref) : kept indices ref = true :=
  Proofs.Formats.Dasl.Arena.Prolly.Sweep.keep_reachable checked reachable

theorem read_kept (swept : sweep? arena roots indices = some view) (external : Reader Name Key Payload)
    {ref : Handle Name} (keep : kept indices ref = true) : view.read external ref = arena.read external ref :=
  Proofs.Formats.Dasl.Arena.Prolly.Sweep.read_kept swept external keep

/-- Exact query observation, including fuel, missing, and malformed blocks.
No completeness, correctness or availability of the external reader is assumed. -/
theorem route_kept [LinearOrder Key] (swept : sweep? arena roots indices = some view)
    (external : Reader Name Key Payload) (width fuel : Nat) (key : Key)
    {expected : Option Nat} {ref : Handle Name} (keep : kept indices ref = true) :
    route (view.read external) width key fuel expected ref = route (arena.read external) width key fuel expected ref :=
  Proofs.Formats.Dasl.Arena.Prolly.Sweep.route_kept swept external width fuel key keep

/-- A single successful sweep preserves queries from *every* declared root
and every structural descendant, not just the most recent root. -/
theorem route_reachable [LinearOrder Key] (swept : sweep? arena roots indices = some view)
    (external : Reader Name Key Payload) (width fuel : Nat) (key : Key)
    {expected : Option Nat} {ref : Handle Name} (reachable : Reachable arena roots ref) :
    route (view.read external) width key fuel expected ref = route (arena.read external) width key fuel expected ref :=
  route_kept swept external width fuel key (keep_reachable (sweep_spec swept).1 reachable)

end Silmaril.Formats.Dasl.Arena.Prolly.Sweep
