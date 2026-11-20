module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Replay.Defs
import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Audit.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReplay

public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Replay

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Wasm.Numerics

/-- Two checked Core exports: the journal records the node commit and the accept, then
the dead-slot diagnostic. The trap adds neither a new tree nor a new move. -/
theorem audited_accepts_then_traps (P : Profile) (rt : RT) (rep : Nat)
    (entry : rt 1 = some ⟨0, rep, true⟩) :
    ∃ mt instanceInfo initial, IsSpecInstance ownMod mt instanceInfo initial ∧
      contract.link ownMod instanceInfo initial 0 = .ok (some 0) ∧
      ∃ afterAccept afterTrap : Store Nat,
        TSession P (Audit.env contract (some 0)) ownMod (some 0) roles initial ⟨⟨rt, {}⟩, []⟩
          instanceInfo.addrs .idle false
          (⟨afterAccept, {}, []⟩, ⟨⟨rt.killAll [1], ⟨none, [resTree rep]⟩⟩, acceptedEntries⟩)
          [.enter none, .exit (some ())] ∧
        contract.attempt (some 0) (rt.killAll [1]) ⟨0, afterTrap, nodeArgs⟩ = .error (.resource (.dead 1)) ∧
        TSession P (Audit.env contract (some 0)) ownMod (some 0) roles initial ⟨⟨rt, {}⟩, []⟩
          instanceInfo.addrs .idle false
          (⟨afterTrap, {}, [.trap]⟩, ⟨⟨rt.killAll [1], ⟨none, [resTree rep]⟩⟩, rejectedEntries⟩)
          [.enter none, .exit (some ()), .enter none, .exit none] :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReplay.audited_accepts_then_traps P rt rep entry

/-- In the linked `ownMod` instance, the first export moves slot `1` and accepts `res(rep)`.
Calling the same export again diagnoses a dead slot and traps, preserving the earlier tree
and consumed table. The stores are observed after each call's own Core memory effects. -/
theorem accepts_then_traps (P : Profile) (rt : RT) (rep : Nat)
    (entry : rt 1 = some ⟨0, rep, true⟩) :
    ∃ mt instanceInfo initial, IsSpecInstance ownMod mt instanceInfo initial ∧
      contract.link ownMod instanceInfo initial 0 = .ok (some 0) ∧
      ∃ afterAccept afterTrap : Store Nat,
        TSession P (contract.env (some 0)) ownMod (some 0) roles initial ⟨rt, {}⟩
          instanceInfo.addrs .idle false
          (⟨afterAccept, {}, []⟩, ⟨rt.killAll [1], ⟨none, [resTree rep]⟩⟩)
          [.enter none, .exit (some ())] ∧
        contract.attempt (some 0) (rt.killAll [1]) ⟨0, afterTrap, nodeArgs⟩ = .error (.resource (.dead 1)) ∧
        TSession P (contract.env (some 0)) ownMod (some 0) roles initial ⟨rt, {}⟩
          instanceInfo.addrs .idle false
          (⟨afterTrap, {}, [.trap]⟩, ⟨rt.killAll [1], ⟨none, [resTree rep]⟩⟩)
          [.enter none, .exit (some ()), .enter none, .exit none] := by
  obtain ⟨mt, inst, initial, spec, linked, afterAccept, afterTrap, accepted, rejected, retried⟩ :=
    audited_accepts_then_traps P rt rep entry
  exact ⟨mt, inst, initial, spec, linked, afterAccept, afterTrap, Audit.erase accepted, rejected, Audit.erase retried⟩

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Replay
