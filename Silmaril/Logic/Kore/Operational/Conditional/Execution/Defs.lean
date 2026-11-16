module

public import Silmaril.Logic.Kore.Operational.Conditional.Defs

/-! Executable exploration of the existing conditional constructor profile.
No priority or first-match policy is introduced. -/
@[expose] public section
namespace Silmaril.Logic.Kore.Operational.Conditional.Execution

/-- A single rule tests the actual head and guard, preserving every other field.
All decisions use the existing computable String/Int/Bool instances. -/
def fire (r : Rule) (c : Config) : Option Config :=
  match c.code with
  | [] => none
  | state :: tail =>
      if state = r.before ∧ r.guard.eval c.val = true then
        some ⟨r.after :: tail, c.val, c.counter⟩
      else none

/-- Enumerate every enabled installed rule in input order. Duplicate rules retain
duplicate successors; membership, rather than uniqueness, models nondeterminism. -/
def successors (rules : List Rule) (c : Config) : List Config :=
  rules.filterMap (fun r => fire r c)

/-- Complete text checking precedes execution. Rejection is none; accepted
deadlock is some [], and claims remain outside the installed axiom list. -/
def successors? (input : String) (c : Config) : Option (List Config) := do
  let program ← check input
  return successors program.axioms c

/-- Independent relational path length, using the existing source Step.
The index counts transitions, including zero for reflexivity. -/
inductive Runs (rules : List Rule) : Nat → Config → Config → Prop
  | refl (c : Config) : Runs rules 0 c c
  | next {n : Nat} {c e d : Config} :
      Step rules c e → Runs rules n e d → Runs rules (n + 1) c d

/-- All endpoints reached in exactly n transitions. A deadlock has no positive
frontier, and no implicit stuttering transition is added. -/
def frontier (rules : List Rule) : Nat → Config → List Config
  | 0, c => [c]
  | n + 1, c => (successors rules c).flatMap (frontier rules n)

/-- Endpoints reachable in at most n transitions, including the initial state.
This finite tree search preserves multiplicity and is not a termination test. -/
def explore (rules : List Rule) (n : Nat) (c : Config) : List Config :=
  (List.range (n + 1)).flatMap (fun k => frontier rules k c)

end Silmaril.Logic.Kore.Operational.Conditional.Execution
