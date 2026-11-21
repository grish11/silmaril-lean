module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Lower.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Lower.Examples

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

def mixedType : TypeOf := .tuple [.option (.future none), .stream (some (.list (.prim .u8)))]

def mixed : Signature := ⟨Unit, fun _ => mixedType, fun _ => .fixed 0⟩

theorem rejects_inactive_allocation :
    let cx : LiftLowerContext Mock.mock := { opts := {}, inst := ⟨0⟩ }
    preflight cx (.option (.list (.future none))) ⟨.variant 0 none, by decide⟩ .flat =
      .error .indirectPayload := by
  dsimp only
  kernel_rfl

inductive Finish where
  | success | memory | bounds | absentDestination

/-- Reject a wrong stream type after preflighting a valid future, then retry the same
tree with its actual type and lower both endpoints together. -/
noncomputable def session (finish : Finish) : P Mock.mock (State mixed) (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let cx : LiftLowerContext Mock.mock := { opts := { memory := some 0 }, inst := ⟨0⟩ }
  let _ ← (Async.Call.create .future none).program limits Quirks.none
  let _ ← (Async.Call.create .stream (some (.list (.prim .u8)))).program limits Quirks.none
  let .ok (.tag label _ _) ← acceptNode mixed limits Quirks.none cx () (.memory 0) []
    | internal "could not accept the mixed compound tree"
  let wrongType : TypeOf := .tuple [.option (.future none), .stream (some (.prim .u16))]
  let .ok wrong ← pure (checkValue wrongType label.2.val)
    | internal "wrong element type should be caught dynamically"
  let .error (.endpoint .wrongType) ← lower limits Quirks.none cx wrongType wrong .flat
    | internal "the wrong element type was not rejected"
  let flatContext : LiftLowerContext Mock.mock := { opts := {}, inst := cx.inst }
  match finish with
  | .bounds =>
    let _ ← lower limits Quirks.none cx mixedType label.2 (.memory 64)
    internal "out-of-bounds direct lowering should trap"
  | .absentDestination =>
    let _ ← lower limits Quirks.none { cx with inst := ⟨1⟩ } mixedType label.2 .flat
    internal "insert into a missing destination table should trap"
  | .memory =>
    let .ok () ← lower limits Quirks.none cx mixedType label.2 (.memory 0)
      | internal "the typed rejection lost an earlier claim"
    pure ()
  | .success =>
    let .ok words ← lower limits Quirks.none flatContext mixedType label.2 .flat
      | internal "the typed rejection lost an earlier claim"
    let reply : List FlatValue := words
    trapIf (reply != [i32Flat 1, i32Flat 3, i32Flat 1]) (.internal "wrong canonical flat reply")
  let .error .unclaimed ← lower limits Quirks.none flatContext mixedType label.2 .flat
    | internal "a stored observation transferred twice"
  pure .unit

noncomputable def initial (finish : Finish) : Machine.Config Mock.mock (State mixed) where
  store := { CStore.empty with
    insts := [{}]
    core := { mems := [⟨.i32, ⟨#[1, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0]⟩⟩] }
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := {}
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) (session finish)]

def noReady : HostReady (State mixed) := fun _ _ => false

noncomputable def noCalls (_ : Canon.Call Mock.mock) : P Mock.mock (State mixed) (Ret Mock.mock) :=
  internal "allocation or call during direct compound lowering"

noncomputable def run (exec : Mock.mock.Exec) (finish : Finish) :=
  Machine.run noReady noCalls exec Machine.Oracle.first 240 (initial finish)

theorem session_sound (exec : Mock.mock.Exec) (finish : Finish) :
    Machine.Steps .deterministic noReady noCalls (initial finish)
      (run exec finish).labels (run exec finish).config :=
  Machine.run_sound noReady noCalls exec Machine.Oracle.first 240 (initial finish)

theorem validated_compound_commits_once (exec : Mock.mock.Exec) :
    let result := run exec .success
    (result.outcome, result.config.host.accepted.map rootIds, result.config.host.held,
      (result.config.store.insts.get? 0).map (fun inst => [inst.handles.get? 1, inst.handles.get? 3])) =
      (.resolved, [[⟨0⟩, ⟨2⟩]], [], some [some (.waitable (.end_ ⟨2⟩)), some (.waitable (.end_ ⟨0⟩))]) := by
  dsimp only
  kernel_rfl

theorem bounds_trap_preserves_both_claims (exec : Mock.mock.Exec) :
    let result := run exec .bounds
    (result.labels.getLast?, result.config.store.lockdown, result.config.host.held) =
      (some (.trap .outOfBounds), true, [⟨0⟩, ⟨2⟩]) := by
  dsimp only
  kernel_rfl

theorem late_table_trap_spends_only_transferred_claim (exec : Mock.mock.Exec) :
    let result := run exec .absentDestination
    (result.labels.getLast?, result.config.store.lockdown, result.config.host.accepted.map rootIds,
      result.config.host.held, (result.config.store.end? ⟨0⟩).map (·.owner)) =
      (some (.trap (.internal "dangling arena id")), true, [[⟨0⟩, ⟨2⟩]], [⟨2⟩], some (some ⟨1⟩)) := by
  dsimp only
  kernel_rfl

theorem validated_compound_writes_canonical_memory (exec : Mock.mock.Exec) :
    let result := run exec .memory
    (result.outcome, result.config.host.held, result.config.store.core.mems[0]?.map (·.bytes.data)) =
      (.resolved, [], some #[1, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0]) := by
  dsimp only
  kernel_rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Lower.Examples
