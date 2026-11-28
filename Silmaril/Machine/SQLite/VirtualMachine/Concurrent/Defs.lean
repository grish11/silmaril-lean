module

public import Silmaril.Machine.SQLite.VirtualMachine.Traced.Defs
public import Silmaril.Semantics.TrackA.Concurrency.Defs
public import Silmaril.Semantics.TrackA.Interaction.UB.Defs

/-! One shared snapshot-generation slot, with optional mutex protection.
A client captures a generation once and runs local fixed bytecode against
that immutable snapshot. Publication changes only the slot; it does not
edit the snapshots or share cursors or registers. The SC trace orders
acquisition, capture, publication and release. A query report is attached
to its capture, so the model does not schedule individual VM instructions.

This is an explicit model of the snapshot selection boundary. It leaves
SQLite connection mutexes, B-tree and pager locks, transaction boundaries,
blocking and busy callbacks, WAL, lock upgrades, fairness, and the memory
behavior of native code unspecified. A race is an attempted racing
extension of a generated Track A SC execution. VM failures and exhaustion
remain ordinary query observations. -/

@[expose] public section

namespace Silmaril.Machine.SQLite.VirtualMachine.Concurrent

open Silmaril.Semantics.TrackA
open Silmaril.Semantics.TrackA.Interaction

inductive Job where
  | idle
  | query (program : Program) (fuel : Nat) (initialState : State)
  | publish (generation : Nat)

structure Client where
  job : Job
  mode : Concurrency.AccessMode := .plain
  mutex : Bool := false

def Client.code (client : Client) : Concurrency.Program Unit Unit :=
  let finish := if client.mutex then Concurrency.Program.release () .done else .done
  let access := match client.job with
    | .idle => .done
    | .query .. => .load client.mode () fun _ => finish
    | .publish generation => .store client.mode () generation finish
  match client.job with
  | .idle => .done
  | _ => if client.mutex then .acquire () access else access

abbrev History (Thread : Type) := List (Concurrency.Event Thread Unit Unit)
abbrev Configuration (Thread : Type) := Concurrency.Config Thread Unit Unit

def initialConfig {Thread : Type} (clients : Thread → Client) (generation : Nat) :
    Configuration Thread :=
  Concurrency.Config.initial (fun thread => (clients thread).code) (fun () => generation)

structure QueryReport (Thread : Type) where
  thread : Thread
  generation : Nat
  execution : Traced.Report
  deriving DecidableEq

structure Report (Thread : Type) where
  history : History Thread
  queries : List (QueryReport Thread)
  deriving DecidableEq

/-- Project queries in the order of their version-slot reads. The caller of
this projection supplies the history; validity comes from replay or the
guarded semantics. -/
def report {Thread : Type} (clients : Thread → Client) (versions : Nat → Database)
    (history : History Thread) : Report Thread :=
  ⟨history, history.filterMap fun event =>
    match event.action, (clients event.thread).job with
    | .read _ () generation, .query code fuel state =>
        some ⟨event.thread, generation, (Traced.runWithTrace (versions generation) code fuel state).report⟩
    | _, _ => none⟩

variable {Thread : Type} [DecidableEq Thread]

/-- The outer Option rejects a disabled schedule. The inner Option is the
Track A explicit UB boundary. The selected SC schedule is finite and can
end before every client has finished. -/
def simulate (profile : Concurrency.RaceProfile) (clients : Thread → Client)
    (versions : Nat → Database) (generation : Nat) (schedule : List Thread) :
    Option (Option (Report Thread)) := do
  let (history, _) ← Concurrency.replay (initialConfig clients generation) schedule
  if Concurrency.hasRace profile history then return none
  else return some (report clients versions history)

/-- Ordinary observations retain the full generated, race-free history.
A UB observation witnesses the first racing extension. Its prefix is
retained in the witness and erased at the whole-run boundary. -/
def explicit (profile : Concurrency.RaceProfile) (clients : Thread → Client)
    (versions : Nat → Database) (generation : Nat) : UB.Explicit (Report Thread) :=
  {out | match out with
    | none => ∃ history, Concurrency.RaceUB profile (initialConfig clients generation) history
    | some observed => ∃ history finish,
        Concurrency.GuardedRun profile (initialConfig clients generation) history finish ∧
          report clients versions history = observed}

def catastrophic (profile : Concurrency.RaceProfile) (clients : Thread → Client)
    (versions : Nat → Database) (generation : Nat) : UB.Catastrophic (Report Thread) :=
  UB.collapse (explicit profile clients versions generation)

end Silmaril.Machine.SQLite.VirtualMachine.Concurrent
