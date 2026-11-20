module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Async.Transfer.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Async.Transfer.Examples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.AsyncRef Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine}

def element : Channel → Element
  | .stream => some (.prim .u8)
  | .future => none

def exampleSession (channel : Channel) : P E Unit (Ret E) := do
  let limits := Component.Limits.spec
  let cx : LiftLowerContext E := { opts := {}, inst := ⟨0⟩ }
  let type := element channel
  let _ ← (Call.create channel type).program limits Quirks.none
  let original ← Endpoint.inspect (channel.endKind .read) type ⟨0⟩ 1
  let .ok transferred ← take limits cx channel type 1
    | internal "typed readable endpoint was not transferred"
  let .error .wrongType ← give limits cx channel (some (.prim .u16)) ⟨transferred.id⟩
    | internal "endpoint could be given with the wrong element type"
  let .ok slot ← give limits cx channel type transferred
    | internal "detached endpoint was not given"
  let restored ← Endpoint.inspect (channel.endKind .read) type ⟨0⟩ slot
  trapIf (original.id != restored.id) (.internal "endpoint identity changed")
  let .error .stillOwned ← give limits cx channel type transferred
    | internal "a duplicate endpoint value regained guest ownership"
  if channel == .future then
    let writable ← Endpoint.inspect .writableFuture type ⟨0⟩ 2
    let _ ← (Call.futureCopy .write type { async_ := true } 2 0).program limits Quirks.none
    let _ ← (Call.futureCopy .read type {} slot 0).program limits Quirks.none
    let _ ← Runtime.Waitable.getPendingEvent (.end_ writable.id)
    pure ()
  let _ ← (Call.close channel .read type slot).program limits Quirks.none
  let _ ← (Call.close channel .write type 2).program limits Quirks.none
  pure .unit

def initial (channel : Channel) : Machine.Config E Unit where
  store := { CStore.empty with
    insts := [{}]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := ()
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) (exampleSession channel)]

def noHostReady : HostReady Unit := fun _ _ => false

def noCalls (_ : Canon.Call E) : P E Unit (Ret E) := internal "unexpected call during transfer"

def run (X : E.Exec) (channel : Channel) :=
  Machine.run noHostReady noCalls X Machine.Oracle.first 180 (initial channel)

theorem transfer_preserves_identity_and_refuses_duplicate (X : E.Exec) (channel : Channel) :
    (run X channel).outcome = .resolved := by
  cases channel <;> kernel_rfl

theorem transfer_session_sound (X : E.Exec) (channel : Channel) :
    Machine.Steps .deterministic noHostReady noCalls (initial (E := E) channel)
      (run X channel).labels (run X channel).config :=
  Machine.run_sound noHostReady noCalls X Machine.Oracle.first 180 (initial channel)

theorem nested_borrow_is_rejected :
    schema (some (.list (.option (.borrow ⟨0⟩)))) = .error .borrowedElement := rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Async.Transfer.Examples
