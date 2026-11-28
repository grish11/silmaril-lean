module

public import Init.Data.List.Find

/-! # Bounded, independently checked worklist receipts -/

@[expose] public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist
universe u v

inductive Stop where
  | fixed
  | exhausted
  deriving DecidableEq

structure Report (Action : Type v) where
  sites : List Action
  stop : Stop

structure Result (State : Type u) (Action : Type v) where
  state : State
  report : Report Action

/-- The producer chooses a site from the current state. The checker
tests each supplied action's enablement independently. -/
structure Driver (State : Type u) (Action : Type v) where
  next : State → Option Action
  enabled : State → Action → Bool
  visit : State → Action → State

variable {State : Type u} {Action : Type v} (driver : Driver State Action)

/-- Charge fuel for visits. Even with zero remaining fuel, check for a
next site before deciding the stop reason. -/
def Driver.run : Nat → State → Result State Action
  | fuel, s =>
    match driver.next s with
    | none => ⟨s, ⟨[], .fixed⟩⟩
    | some action =>
      match fuel with
      | 0 => ⟨s, ⟨[], .exhausted⟩⟩
      | fuel + 1 =>
        let rest := run fuel (driver.visit s action)
        ⟨rest.state, ⟨action :: rest.report.sites, rest.report.stop⟩⟩
termination_by structural fuel _ => fuel

def Driver.replay : State → List Action → Option State
  | s, [] => some s
  | s, action :: more =>
    if driver.enabled s action then replay (driver.visit s action) more else none

def Driver.checkStop (fuel : Nat) (state : State) (report : Report Action) : Bool :=
  match report.stop with
  | .fixed => (driver.next state).isNone
  | .exhausted => decide (report.sites.length = fuel) && (driver.next state).isSome

def Driver.check (fuel : Nat) (source : State) (report : Report Action) : Option State :=
  if report.sites.length ≤ fuel then
    match driver.replay source report.sites with
    | none => none
    | some state => if driver.checkStop fuel state report then some state else none
  else none

end Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist
