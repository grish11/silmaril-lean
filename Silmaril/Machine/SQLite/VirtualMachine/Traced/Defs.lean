module

public import Mathlib.Data.Set.Basic
public import Silmaril.Machine.SQLite.VirtualMachine.Defs

/-! Bounded fixed-code execution with ordered effects. Each run selects a
whole immutable database from the allowed set. This choice can model an
unresolved snapshot and is shared by all opens in the run. -/

@[expose] public section

namespace Silmaril.Machine.SQLite.VirtualMachine.Traced

open Silmaril.Formats.Sqlite

inductive Event where
  | openRead (database root : Nat) (admitted : Bool)
  | row (cells : List Value)
  deriving DecidableEq

/-- A fetched open emits one attempt, including missing-table failure. A
successful ResultRow emits cells in increasing register order. Other
instructions are silent, including erroneous fetches. -/
def stepWithTrace (db : Database) (code : Program) (s : State) :
    List Event × Except Fault State :=
  let next := step db code s
  let events := if s.halted.isSome then [] else
    match code[s.pc]?, next with
    | some (.openRead _ root database), .ok _ => [.openRead database root true]
    | some (.openRead _ root database), .error _ => [.openRead database root false]
    | some (.resultRow first count), .ok _ =>
        [.row ((List.range count).map fun offset => s.registers (first + offset))]
    | _, _ => []
  (events, next)

structure Execution where
  events : List Event
  result : RunResult

def runWithTrace (db : Database) (code : Program) : Nat → State → Execution
  | fuel, s =>
      if s.halted.isSome then ⟨[], .halted s⟩ else
        match fuel with
        | 0 => ⟨[], .exhausted s⟩
        | fuel + 1 =>
          let (events, next) := stepWithTrace db code s
          match next with
          | .error fault => ⟨events, .fault fault s⟩
          | .ok after =>
            let rest := runWithTrace db code fuel after
            ⟨events ++ rest.events, rest.result⟩

structure Report where
  events : List Event
  observation : Observation
  deriving DecidableEq

def Execution.report (execution : Execution) : Report :=
  ⟨execution.events, observe execution.result⟩

def behaviors (snapshots : Set Database) (code : Program) (fuel : Nat) (start : State) :
    Set Report :=
  {out | ∃ db ∈ snapshots, (runWithTrace db code fuel start).report = out}

/-- May refinement is inclusion from implementation into specification.
Equality inside a report observes event order, row order, and termination. -/
def Refines (implementation specification : Set Report) : Prop :=
  implementation ⊆ specification

/-- Total correctness within the fuel bound, for every eligible snapshot.
The existence conjunct rules out vacuous success with no eligible inputs. -/
def WP (runs : Set Report) (post : Report → Prop) : Prop :=
  runs.Nonempty ∧ ∀ report ∈ runs, report.observation.termination = .halted 0 ∧ post report

def Defined (runs : Set Report) : Prop := WP runs fun _ => True

/-- Equality of ordered behavior sets on the domain of defined runs. -/
def Equivalent (left right : Set Report) : Prop := Defined left ∧ left = right

end Silmaril.Machine.SQLite.VirtualMachine.Traced
