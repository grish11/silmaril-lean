module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Future.Examples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.AsyncRef Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Element Endpoint)

def element : Element := some (.record [("word", .prim .u16), ("hint", .option (.prim .bool))])

def signature : Signature := ⟨Unit, fun _ => .option (.future element), fun _ => .fixed 0⟩

noncomputable def invoke (call : Async.Call Mock.mock) : P Mock.mock (State signature) (List FlatValue) :=
  call.program Component.Limits.spec Quirks.none

/-- The reader cancels once before any write. Its saved continuation then reads
the compound element from the independent writer instance. -/
noncomputable def reader : P Mock.mock (State signature) (Ret Mock.mock) := do
  let opts : CanonOpts Mock.mock := { memory := some 1, async_ := true }
  let cx : LiftLowerContext Mock.mock := { opts := opts, inst := ⟨1⟩ }
  let blockedRead ← invoke (.futureCopy .read element opts 1 0)
  trapIf (blockedRead != [i32Flat blocked]) (.internal "future read did not block")
  let cancel ← invoke (.cancel .future .read element true 1)
  trapIf (cancel != [i32Flat (futureCopyPayload .cancelled)]) (.internal "future read did not cancel")
  let untouched ← readMem cx 0 4
  trapIf (untouched.data != #[0, 0, 0, 0]) (.internal "cancelled read wrote its destination")
  block (some ⟨0⟩)
  let completed ← invoke (.futureCopy .read element opts 1 0)
  trapIf (completed != [i32Flat (futureCopyPayload .completed)]) (.internal "future read did not finish")
  let _ ← invoke (.close .future .read element 1)
  pure .unit

/-- Move the future into a typed tree, give it to the reader exactly once, and
poll for completion of the write after the reader's retry. -/
noncomputable def writer : P Mock.mock (State signature) (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let writerCx : LiftLowerContext Mock.mock := { opts := { memory := some 0 }, inst := ⟨0⟩ }
  let readerCx : LiftLowerContext Mock.mock := { opts := { memory := some 1 }, inst := ⟨1⟩ }
  let opts : CanonOpts Mock.mock := { memory := some 0, async_ := true }
  let _ ← invoke (.create .future element)
  let readable ← Endpoint.inspect .readableFuture element ⟨0⟩ 1
  let .ok tree ← acceptNode signature limits Quirks.none writerCx () (.flat [i32Flat 1, i32Flat 1]) []
    | internal "could not accept the typed future"
  trapIf (rootIds tree != [readable.id]) (.internal "accepted tree did not retain the future")
  let .ok 1 ← give limits readerCx .future element readable
    | internal "could not return the claimed future"
  let .error .unclaimed ← give limits readerCx .future element readable
    | internal "the accepted tree transferred its readable future twice"
  block (some ⟨1⟩)
  let _ ← invoke .createSet
  let _ ← invoke (.join 2 1)
  let blockedWrite ← invoke (.futureCopy .write element opts 2 0)
  trapIf (blockedWrite != [i32Flat blocked]) (.internal "future write did not block")
  let noEvent ← invoke (.poll 0 1 4)
  trapIf (noEvent != [i32Flat EventCode.none.toNat]) (.internal "pending write was reported ready")
  resumeThread ⟨1⟩
  let event ← invoke (.poll 0 1 4)
  trapIf (event != [i32Flat EndKind.writableFuture.eventCode.toNat])
    (.internal "poll did not deliver the completed write")
  let _ ← invoke (.join 2 0)
  let _ ← invoke (.closeSet 1)
  let _ ← invoke (.close .future .write element 2)
  pure .unit

noncomputable def initial : Machine.Config Mock.mock (State signature) where
  store := { CStore.empty with
    core := { mems := [⟨.i32, ⟨#[0x34, 0x12, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]⟩⟩,
      ⟨.i32, ⟨#[0, 0, 0, 0]⟩⟩] }
    insts := [{}, {}]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ },
      { ft := ⟨[], none, false⟩, opts := {}, inst := ⟨1⟩, caller := ⟨1⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }, { status := .blocked, task := ⟨1⟩ }] }
  host := {}
  conts := [none, some (Machine.Activation.ofProg (some ⟨1⟩) reader)]
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) writer]

def noReady : HostReady (State signature) := fun _ _ => false

noncomputable def noCalls (_ : Canon.Call Mock.mock) : P Mock.mock (State signature) (Ret Mock.mock) :=
  internal "unexpected call during compound future copy"

noncomputable def run (exec : Mock.mock.Exec) :=
  Machine.run noReady noCalls exec Machine.Oracle.first 360 initial

theorem session_sound (exec : Mock.mock.Exec) :
    Machine.Steps .deterministic noReady noCalls initial (run exec).labels (run exec).config :=
  Machine.run_sound noReady noCalls exec Machine.Oracle.first 360 initial

theorem future_handoff_cancel_retry_and_copy (exec : Mock.mock.Exec) :
    let result := run exec
    (result.outcome, result.config.host.accepted.map rootIds, result.config.host.held,
      result.config.store.core.mems.map (·.bytes.data),
      result.config.store.insts.map (fun inst => [1, 2].map inst.handles.get?)) =
      (.resolved, [[⟨0⟩]], [], [#[0x34, 0x12, 1, 1] ++ (u32Bytes 2).data ++
        (u32Bytes (futureCopyPayload .completed)).data, #[0x34, 0x12, 1, 1]],
        [[none, none], [none, none]]) := by
  dsimp only
  kernel_rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Future.Examples
