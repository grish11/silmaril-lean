module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Resources.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Resources.Examples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine}

def initial (body : P E Unit (Ret E)) : Machine.Config E Unit where
  store := { CStore.empty with
    insts := [{}]
    resourceTypes := [{ impl := some ⟨0⟩ }, { impl := some ⟨0⟩ }]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := ()
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) body]

def noHostReady : HostReady Unit := fun _ _ => false

def noForeignCalls (_ : Canon.Call E) : P E Unit (Ret E) :=
  internal "unexpected foreign call in resource session"

def verifyDtor (inst : InstId) (request : DtorRequest E) : P E Unit Unit :=
  trapIf (inst != ⟨0⟩ || request.rt != ⟨0⟩ || request.rep != 9)
    (.internal "unexpected destructor request")

def invoke (call : Resources.Call) := call.program Component.Limits.spec Quirks.none (verifyDtor (E := E))

def currentTake (resource : RtId) (slot : Nat) : P E Unit (Owned resource) :=
  take Component.Limits.spec { opts := {}, inst := ⟨0⟩ } resource slot

def reuseSession : P E Unit (Ret E) := do
  let firstSlot ← invoke (.create ⟨0⟩ 77)
  let first ← currentTake ⟨0⟩ 1
  let secondSlot ← invoke (.create ⟨0⟩ 77)
  let rep ← invoke (.representation ⟨0⟩ 1)
  let second ← currentTake ⟨0⟩ 1
  trapIf (firstSlot != [i32Flat 1] || firstSlot != secondSlot || rep != [i32Flat 77] ||
    first.identity == second.identity || first.representation != second.representation)
    (.internal "incorrect slot reuse or owning identity")
  let _ ← invoke (.create ⟨0⟩ 9)
  let _ ← invoke (.drop ⟨0⟩ 1)
  pure .unit

def wrongTypeSession : P E Unit (Ret E) := do
  let _ ← invoke (.create ⟨0⟩ 77)
  let _ ← currentTake ⟨1⟩ 1
  pure .unit

def run (X : E.Exec) (body : P E Unit (Ret E)) :=
  Machine.run noHostReady noForeignCalls X Machine.Oracle.first 160 (initial body)

theorem repeated_slot_has_distinct_owners (X : E.Exec) :
    let result := run X reuseSession
    (result.outcome, (result.config.store.insts.get? 0).map (fun inst => inst.handles.get? 1)) =
      (.resolved, some none) := by
  dsimp only
  kernel_rfl

theorem wrong_type_trap_keeps_early_removal (X : E.Exec) :
    let result := run X wrongTypeSession
    (result.config.store.lockdown, (result.config.store.insts.get? 0).map (fun inst => inst.handles.get? 1)) =
      (true, some none) := by
  dsimp only
  kernel_rfl

theorem resource_sessions_sound (X : E.Exec) (body : P E Unit (Ret E)) :
    Machine.Steps .deterministic noHostReady noForeignCalls (initial body)
      (run X body).labels (run X body).config :=
  Machine.run_sound noHostReady noForeignCalls X Machine.Oracle.first 160 (initial body)

end Silmaril.Wasm.Game.HandleAccept.Wit.Resources.Examples
