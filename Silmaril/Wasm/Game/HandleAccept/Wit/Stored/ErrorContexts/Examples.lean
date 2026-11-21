module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.ErrorContexts.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Canon.Builtins.ErrorContext.Defs
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.ErrorContexts.Examples

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value

def signature : Signature :=
  ⟨Unit, fun _ => .option .errorContext, fun _ => .fixed 0⟩

noncomputable def acceptedPayload : Tree signature → Val
  | .atom impossible => impossible.elim
  | .tag label _ _ => label.2.val

/-- Lift an error context inside a tree, drop its original guest slot, reject an absent
arena identity and give the same retained object to the guest twice. Dropping one copy
must not invalidate the other slot. -/
noncomputable def copy : P Mock.mock (List (Tree signature)) (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let cx : LiftLowerContext Mock.mock := { opts := {}, inst := ⟨0⟩ }
  let [slot] ← Builtins.errorContextNew limits Quirks.none cx.opts 0 0
    | internal "unexpected error-context.new result"
  let .ok tree ← buildNode signature limits Quirks.none cx () (.flat [i32Flat 1, slot]) []
    | internal "error context was not lifted"
  let .variant 1 (some (.errorContext id)) := acceptedPayload tree
    | internal "wrong constructor in lifted tree"
  record signature tree
  let _ ← Builtins.errorContextDrop 1
  let .error .missingContext ← give limits cx ⟨1⟩
    | internal "absent context allocated a slot"
  let .ok first ← give limits cx id
    | internal "could not reissue dropped context"
  let .ok second ← give limits cx id
    | internal "copy incorrectly spent the context"
  let _ ← Builtins.errorContextDrop first
  let returned ← liftErrorContext limits cx second
  if returned != id then internal "copy did not retain the arena identity"
  return .unit

noncomputable def initial : Machine.Config Mock.mock (List (Tree signature)) where
  store := { CStore.empty with
    insts := [{}]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := []
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) copy]

noncomputable def noReady : HostReady (List (Tree signature)) := fun _ _ => false

noncomputable def noCalls (_ : Canon.Call Mock.mock) : P Mock.mock (List (Tree signature)) (Ret Mock.mock) :=
  internal "unexpected error-context call"

noncomputable def run (engine : Mock.mock.Exec) :=
  Machine.run noReady noCalls engine Machine.Oracle.first 96 initial

theorem copy_sound (engine : Mock.mock.Exec) :
    Machine.Steps .deterministic noReady noCalls initial (run engine).labels (run engine).config :=
  Machine.run_sound noReady noCalls engine Machine.Oracle.first 96 initial

theorem copies_survive_independent_drop (engine : Mock.mock.Exec) :
    let result := run engine
    (result.outcome, result.config.host.map acceptedPayload,
      (result.config.store.insts.get? 0).map (fun inst => [inst.handles.get? 1, inst.handles.get? 2])) =
      (.resolved, [.variant 1 (some (.errorContext ⟨0⟩))], some [none, some (.errCtx ⟨0⟩)]) := by
  dsimp only
  kernel_rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.ErrorContexts.Examples
