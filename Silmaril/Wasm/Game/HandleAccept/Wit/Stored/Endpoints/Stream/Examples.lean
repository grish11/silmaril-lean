module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Canon.Builtins.Resource.Defs
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Stream.Examples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.AsyncRef Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Element Endpoint)

private def resource : RtId := ⟨0⟩

def element : Element := some (.record [("word", .prim .u16), ("item", .own resource)])

def signature : Signature := ⟨Unit, fun _ => .option (.stream element), fun _ => .fixed 0⟩

private def limits := Component.Limits.spec

private noncomputable def invoke (call : Async.Call Mock.mock) :
    P Mock.mock (State signature) (List FlatValue) :=
  call.program limits Quirks.none

private noncomputable def reader (stale : Bool) : P Mock.mock (State signature) (Ret Mock.mock) := do
  let opts : CanonOpts Mock.mock := { memory := some 1, async_ := true }
  let cx : LiftLowerContext Mock.mock := { opts := opts, inst := ⟨1⟩ }
  let blockedRead ← invoke (.streamCopy .read element opts 1 0 2)
  trapIf (blockedRead != [i32Flat blocked]) (.internal "stream read did not block")
  let cancelled ← invoke (.cancel .stream .read element true 1)
  trapIf (cancelled != [i32Flat (packStreamCopyResult .cancelled 0)])
    (.internal "stream read did not cancel")
  let untouched ← readMem cx 0 16
  trapIf (untouched.data != #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    (.internal "cancelled stream wrote to the destination")
  block (some ⟨0⟩)
  let completed ← invoke (.streamCopy .read element opts 1 0 2)
  trapIf (completed != [i32Flat (packStreamCopyResult .completed 2)])
    (.internal "stream did not copy both records")
  let first ← Builtins.resourceRep limits resource 2
  let second ← Builtins.resourceRep limits resource 3
  trapIf (first != [i32Flat 71] || second != [i32Flat 93])
    (.internal "stream did not transfer the owners in order")
  let _ ← Builtins.resourceDrop limits Quirks.none (checkDrop 71) resource 2
  let _ ← Builtins.resourceDrop limits Quirks.none (checkDrop 93) resource 3
  block none
  let closed ← invoke (.streamCopy .read element opts 1 0 2)
  trapIf (closed != [i32Flat (packStreamCopyResult .dropped 0)])
    (.internal "stream read did not observe its writer closing")
  let _ ← invoke (.close .stream .read element 1)
  if stale then
    let _ ← invoke (.streamCopy .read element opts 1 0 2)
    pure .unit
  else pure .unit
where
  checkDrop (rep : Nat) (inst : InstId) (request : DtorRequest Mock.mock) :
      P Mock.mock (State signature) Unit :=
    trapIf (inst != ⟨1⟩ || request.rt != resource || request.rep != rep)
      (.internal "destructor did not receive the moved owner")

private noncomputable def writer : P Mock.mock (State signature) (Ret Mock.mock) := do
  let writerCx : LiftLowerContext Mock.mock := { opts := { memory := some 0 }, inst := ⟨0⟩ }
  let readerCx : LiftLowerContext Mock.mock := { opts := { memory := some 1 }, inst := ⟨1⟩ }
  let opts : CanonOpts Mock.mock := { memory := some 0, async_ := true }
  let _ ← invoke (.create .stream element)
  let _ ← Builtins.resourceNew limits resource 71
  let _ ← Builtins.resourceNew limits resource 93
  let readable ← Endpoint.inspect .readableStream element ⟨0⟩ 1
  let .ok tree ← acceptNode signature limits Quirks.none writerCx () (.flat [i32Flat 1, i32Flat 1]) []
    | internal "could not accept the typed stream"
  trapIf (rootIds tree != [readable.id]) (.internal "the accepted stream did not retain its identity")
  let .ok 1 ← give limits readerCx .stream element readable
    | internal "could not give the claimed stream to the reader"
  let .error .unclaimed ← give limits readerCx .stream element readable
    | internal "could give away the stream observation twice"
  block (some ⟨1⟩)
  let _ ← invoke .createSet
  let _ ← invoke (.join 2 1)
  let pending ← invoke (.streamCopy .write element opts 2 0 2)
  trapIf (pending != [i32Flat blocked]) (.internal "stream write did not block")
  let noEvent ← invoke (.poll 0 1 16)
  trapIf (noEvent != [i32Flat EventCode.none.toNat]) (.internal "pending stream write was reported ready")
  resumeThread ⟨1⟩
  let event ← invoke (.poll 0 1 16)
  trapIf (event != [i32Flat EndKind.writableStream.eventCode.toNat])
    (.internal "completed stream write was not reported ready")
  let _ ← invoke (.join 2 0)
  let _ ← invoke (.closeSet 1)
  let _ ← invoke (.close .stream .write element 2)
  resumeThread ⟨1⟩
  pure .unit

private noncomputable def initial (stale : Bool) : Machine.Config Mock.mock (State signature) where
  store := { CStore.empty with
    core := { mems := [⟨.i32, ⟨#[12, 0, 0, 0, 3, 0, 0, 0, 31, 0, 0, 0, 4, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0]⟩⟩, ⟨.i32, ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩⟩] }
    insts := [{}, {}]
    resourceTypes := [{ impl := some ⟨0⟩ }]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ },
      { ft := ⟨[], none, false⟩, opts := {}, inst := ⟨1⟩, caller := ⟨1⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }, { status := .blocked, task := ⟨1⟩ }] }
  host := {}
  conts := [none, some (Machine.Activation.ofProg (some ⟨1⟩) (reader stale))]
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) writer]

private def noReady : HostReady (State signature) := fun _ _ => false

private noncomputable def noCalls (_ : Canon.Call Mock.mock) : P Mock.mock (State signature) (Ret Mock.mock) :=
  internal "unexpected component call during stream copy"

private noncomputable def run (exec : Mock.mock.Exec) (stale : Bool) :=
  Machine.run noReady noCalls exec Machine.Oracle.first 520 (initial stale)

theorem session_sound (exec : Mock.mock.Exec) (stale : Bool) :
    Machine.Steps .deterministic noReady noCalls (initial stale) (run exec stale).labels
      (run exec stale).config :=
  Machine.run_sound noReady noCalls exec Machine.Oracle.first 520 (initial stale)

theorem stream_transfers_owners_once_and_closes (exec : Mock.mock.Exec) :
    let result := run exec false
    (result.outcome, result.config.host.accepted.map rootIds, result.config.host.held,
      (result.config.store.core.mems[1]?).map (·.bytes.data),
      result.config.store.insts.map (fun inst => [1, 2, 3, 4].map inst.handles.get?)) =
      (.resolved, [[⟨0⟩]], [], some #[12, 0, 0, 0, 2, 0, 0, 0, 31, 0, 0, 0, 3, 0, 0, 0],
        [[none, none, none, none], [none, none, none, none]]) := by
  dsimp only
  kernel_rfl

theorem stale_stream_slot_traps_without_erasing_the_tree (exec : Mock.mock.Exec) :
    let result := run exec true
    (result.labels.any (fun | .trap (.unknownHandle 1) => true | _ => false),
      result.config.host.accepted.map rootIds, result.config.host.held) = (true, [[⟨0⟩]], []) := by
  dsimp only
  kernel_rfl

theorem stream_element_borrow_rejects_before_lift :
    checkSchema (.option (.stream (some (.option (.borrow resource))))) = .error .storedBorrow := rfl

theorem inactive_direct_owner_still_rejects :
    checkSchema (.result (some (.stream element)) (some (.list (.own resource)))) =
      .error .ownedResourceNeedsIdentity := rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Stream.Examples
