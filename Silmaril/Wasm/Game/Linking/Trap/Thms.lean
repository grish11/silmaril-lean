module

public import Silmaril.Wasm.Game.Machine.Thms
import Silmaril.Proofs.Wasm.Game.Linking.Split.Typed

public section

namespace Silmaril.Wasm.Game.Linking

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.SingleThreaded

/-- A trap in a host-call context unwinds without another host call or a change to the store. -/
theorem fill_trap_steps (P : Profile) (store : Store Nat) (ctx : Ctx) (frame : Frame) :
    Steps P (fun _ _ _ _ => False) ⟨store, frame, ctx.fill [.trap]⟩ ⟨store, frame, [.trap]⟩ :=
  Reach.steps (Silmaril.Proofs.Wasm.Game.Linking.Split.fill_trap_reach P store ctx frame)

end Silmaril.Wasm.Game.Linking
