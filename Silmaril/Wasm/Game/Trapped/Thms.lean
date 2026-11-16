module

public import Silmaril.Wasm.Game.Machine.Defs
import Silmaril.Proofs.Wasm.Game.Machine.Doomed

/-!
# Trapped configurations terminate: theorems

A header for `Silmaril.Proofs.Wasm.Game.Machine.Doomed`, for users outside the `Wasm.Game`
topic. Every profile `P`:

* `trapped_step_lt`: every host-free Core step from a trapped configuration `E.fill [TRAP]` (a
  `TRAP` under a callout context) strictly decreases the size of the code. With
  `Choice.step_doomed` (such steps keep the configuration trapped, in the same store and frame)
  this is the measure excluding infinite host-free runs from a trapped configuration.

Proofs: `Silmaril.Proofs.Wasm.Game.Machine.Doomed`.
-/

public section

namespace Silmaril.Wasm.Game

open Silmaril.Wasm.Execution.Core (Store Frame Config Step)
open Silmaril.Wasm.Numerics (Profile)

/-- **Every host-free step of a trapped configuration decreases the size of the code.** -/
theorem trapped_step_lt {H : Type} {P : Profile} {E : Silmaril.Wasm.SingleThreaded.Ctx}
    {s : Store H} {f : Frame} {d : Config H}
    (h : Step P Silmaril.Wasm.SingleThreaded.Det.noHost ⟨s, f, E.fill [.trap]⟩ d) :
    sizeOf d.code < sizeOf (E.fill [.trap]) :=
  Silmaril.Proofs.Wasm.Game.Choice.trapped_step_lt h

end Silmaril.Wasm.Game
