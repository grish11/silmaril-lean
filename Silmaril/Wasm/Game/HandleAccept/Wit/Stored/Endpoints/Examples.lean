module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Examples

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.AsyncRef
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Element Endpoint)

def byteElement : Element := some (.prim .u8)

def mixed : Signature :=
  ⟨Unit, fun _ => .tuple [.option (.future none), .stream byteElement], fun _ => .fixed 0⟩

noncomputable def invoke (call : Async.Call Mock.mock) : P Mock.mock (State mixed) (List FlatValue) :=
  call.program Component.Limits.spec Quirks.none

noncomputable def mixedSession : P Mock.mock (State mixed) (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let cx : LiftLowerContext Mock.mock := { opts := { memory := some 0 }, inst := ⟨0⟩ }
  let opts : CanonOpts Mock.mock := { memory := some 0, async_ := true }
  let _ ← invoke (.create .future none)
  let _ ← invoke (.create .stream byteElement)
  let future ← Endpoint.inspect .readableFuture none ⟨0⟩ 1
  let stream ← Endpoint.inspect .readableStream byteElement ⟨0⟩ 3
  let .error .unclaimed ← give limits cx .future none future
    | internal "a guest observation provided host authority"
  let .ok tree ← acceptNode mixed limits Quirks.none cx () (.memory 0) []
    | internal "could not lift the combined tree"
  trapIf (rootIds tree != [future.id, stream.id]) (.internal "lift changed endpoint identities")
  let .error (.give .wrongType) ← give limits cx .stream (some (.prim .u16)) ⟨stream.id⟩
    | internal "could give a stream at the wrong element type"
  let .ok futureSlot ← give limits cx .future none future
    | internal "could not give the lifted future"
  let .error .unclaimed ← give limits cx .future none future
    | internal "an accepted tree could give its future twice"
  let .ok streamSlot ← give limits cx .stream byteElement stream
    | internal "could not give the lifted stream"
  let futureAfter ← Endpoint.inspect .readableFuture none ⟨0⟩ futureSlot
  let streamAfter ← Endpoint.inspect .readableStream byteElement ⟨0⟩ streamSlot
  trapIf (futureAfter.id != future.id || streamAfter.id != stream.id)
    (.internal "give changed endpoint identities")
  let writer ← Endpoint.inspect .writableFuture none ⟨0⟩ 2
  let _ ← invoke (.futureCopy .write none { async_ := true } 2 0)
  let _ ← invoke (.futureCopy .read none {} futureSlot 0)
  let _ ← Runtime.Waitable.getPendingEvent (.end_ writer.id)
  let writeReply ← invoke (.streamCopy .write byteElement opts 4 12 2)
  trapIf (writeReply != [i32Flat blocked]) (.internal "stream write was not pending")
  let readReply ← invoke (.streamCopy .read byteElement opts streamSlot 14 2)
  trapIf (readReply != [i32Flat (packStreamCopyResult .completed 2)])
    (.internal "stream did not deliver two values")
  let _ ← Runtime.Waitable.getPendingEvent (.end_ (← Endpoint.inspect .writableStream byteElement ⟨0⟩ 4).id)
  let _ ← invoke (.close .future .read none futureSlot)
  let _ ← invoke (.close .future .write none 2)
  let _ ← invoke (.close .stream .read byteElement streamSlot)
  let _ ← invoke (.close .stream .write byteElement 4)
  pure .unit

noncomputable def initial : Machine.Config Mock.mock (State mixed) where
  store := { CStore.empty with
    core := { mems := [⟨.i32, ⟨#[1, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 41, 97, 0, 0]⟩⟩] }
    insts := [{}]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := {}
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) mixedSession]

def noReady : HostReady (State mixed) := fun _ _ => false

noncomputable def noCalls (_ : Canon.Call Mock.mock) : P Mock.mock (State mixed) (Ret Mock.mock) :=
  internal "unexpected call during endpoint handoff"

noncomputable def run (exec : Mock.mock.Exec) :=
  Machine.run noReady noCalls exec Machine.Oracle.first 360 initial

theorem mixed_tree_transfers_once_and_stream_delivers_bytes (exec : Mock.mock.Exec) :
    let result := run exec
    (result.outcome, result.config.host.accepted.map rootIds, result.config.host.held,
      result.config.store.core.mems.head?.map (·.bytes.data)) =
      (.resolved, [[⟨0⟩, ⟨2⟩]], [], some #[1, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 41, 97, 41, 97]) := by
  dsimp only
  kernel_rfl

theorem mixed_session_sound (exec : Mock.mock.Exec) :
    Machine.Steps .deterministic noReady noCalls initial (run exec).labels (run exec).config :=
  Machine.run_sound noReady noCalls exec Machine.Oracle.first 360 initial

/-- A malformed destination fixture traps at instance lookup, after the owner update.
This exercises the same prefix as a full reference table without allocating it. -/
noncomputable def lateTrap : P Mock.mock (State mixed) (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let cx : LiftLowerContext Mock.mock := { opts := { memory := some 0 }, inst := ⟨0⟩ }
  let _ ← invoke (.create .future none)
  let _ ← invoke (.create .stream byteElement)
  let .ok _ ← acceptNode mixed limits Quirks.none cx () (.memory 0) []
    | internal "could not lift the trap fixture"
  let _ ← give limits { cx with inst := ⟨1⟩ } .future none ⟨⟨0⟩⟩
  pure .unit

noncomputable def lateInitial : Machine.Config Mock.mock (State mixed) :=
  { initial with ctl := [Machine.Activation.ofProg (some ⟨0⟩) lateTrap] }

noncomputable def runLate (exec : Mock.mock.Exec) :=
  Machine.run noReady noCalls exec Machine.Oracle.first 160 lateInitial

theorem late_trap_trace_sound (exec : Mock.mock.Exec) :
    Machine.Steps .deterministic noReady noCalls lateInitial (runLate exec).labels (runLate exec).config :=
  Machine.run_sound noReady noCalls exec Machine.Oracle.first 160 lateInitial

theorem late_trap_spends_only_the_moved_claim (exec : Mock.mock.Exec) :
    let result := runLate exec
    (result.labels.any (fun label => match label with
      | .trap (.internal "dangling arena id") => true
      | _ => false), result.config.host.held, result.config.host.accepted.map rootIds,
      (result.config.store.end? ⟨0⟩).map (fun endpoint => (endpoint.owner, endpoint.index))) =
      (true, [⟨2⟩], [[⟨0⟩, ⟨2⟩]], some (some ⟨1⟩, none)) := by
  dsimp only
  kernel_rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Examples
