module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Singleton.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable.Thms
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Singleton.Defs

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Singleton.Regression

open NestedTheta.Liveness
open Continuation (Stack)
open Continuation.Partial (Config Step)
open Continuation.Partial.Executable (Actions Observation next? observe runFor runFor_add step_iff)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev single := [num]
private abbrev pair := [num, num]
private abbrev fn : Function Unit Unit := ⟨[num, num, num], pair⟩
private abbrev entry := [fn.port, num, num, num, num]
private abbrev decision : List T := [.control 2, num]

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | route : Op single decision
  | probe : Op single []
  | after : Op [] []

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .route, .cons (.data count) .nil => .cons (.control 0) (.cons (.data count) .nil)
    | .probe, _ => .nil
    | .after, _ => .nil

private def one (n : Nat) : Tuple machine.Val single := .cons (.data n) .nil
private def two (a b : Nat) : Tuple machine.Val pair := .cons (.data a) (one b)

private def actions : Actions machine Nat where
  step
    | .route, .cons (.data count) .nil => fun store =>
      let count : Nat := count
      let tag : Fin 2 := if count = 0 then 0 else 1
      let next := if count = 99 then count else count - 1
      some (.cons (.control tag) (one next), store + 1)
    | .probe, .cons (.data cap) .nil => fun store =>
      let cap : Nat := cap
      if cap = 0 then none else some (.nil, store + cap)
    | .after, _ => fun store => some (.nil, store + 10)

private def required (demand : Demand) : List Address :=
  [.arg 0, .arg 1] ++ (if demand 0 then [.arg 2] else []) ++ (if demand 1 then [.arg 3] else [])

private abbrev summary : MemberSummary Unit Unit where
  fn := fn
  captures := single
  live := required
  monotone := by
    intro low high le
    have selected (p : Nat) (a : Address) :
        (if low p then [a] else []) ⊆ (if high p then [a] else []) := by
      intro b h
      by_cases active : low p = true
      · simpa only [ite_eq_left active, ite_eq_left (le p active)] using h
      · simp [active] at h
    intro a h
    simp only [required, List.mem_append] at h ⊢
    exact h.imp (fun h => h.imp id (fun h => selected 0 _ h)) (fun h => selected 1 _ h)

private def capture : Port entry num := .tail .head
private def count : Port entry num := .tail (.tail .head)
private def payload : Port entry num := .tail (.tail (.tail .head))
private def spare : Port entry num := .tail (.tail (.tail (.tail .head)))

private def baseArm : Code Op entry [] [[]] pair true (some summary) :=
  .primitive .probe (.cons (.arg capture) .nil)
    (.ret (.cons (.arg payload) (.cons (.arg spare) .nil)))

private def recursiveArm : Code Op entry [] [pair, []] pair true (some summary) :=
  .memberCall (summary := summary) .head (.cons (.arg capture) .nil)
    (.cons (.arg count) (.cons (.arg payload) (.cons (.arg spare) .nil)))
    (.primitive .after .nil
      (.ret (.cons (.output (0 : Fin 2) .head) (.cons (.output (0 : Fin 2) (.tail .head)) .nil))))

private def armSigs : Fin 2 → List (Ports T) := Fin.cases [[]] (fun _ => [pair, []])

private def arms (i : Fin 2) : Code Op entry [] (armSigs i) pair true (some summary) :=
  Fin.cases (motive := fun j => Code Op entry [] (armSigs j) pair true (some summary))
    baseArm (fun _ => recursiveArm) i

private def body : Code Op entry [] [decision, pair] pair true (some summary) :=
  let captures : Wires entry [decision] entry :=
    .cons (.arg .head) (.cons (.arg capture) (.cons (.output (0 : Fin 1) (.tail .head))
      (.cons (.arg payload) (.cons (.arg spare) .nil))))
  .primitive .route (.cons (.arg count) .nil)
    (.gamma 0 armSigs (.output (0 : Fin 1) .head) captures arms
      (.ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))))

private theorem body_live (d : Demand) :
    (body.plan d).live =
      [.arg 2, .arg 1] ++ (if d 0 then [.arg 3] else []) ++ (if d 1 then [.arg 4] else []) := by
  cases h0 : d 0 <;> cases h1 : d 1 <;>
    simp (config := { decide := true }) [body, arms, armSigs, baseArm, recursiveArm, capture, count, payload,
      spare, summary, Code.plan, DemandPlan.prepend, transfer, selectWires,
      Demand.observes, NestedTheta.Kind.demandReads, Wires.addresses, Origin.address, Port.index, definedAt,
      h0, h1]

private def family : Singleton Op summary single where
  captures := .cons (.arg .head) .nil
  memberWires := .cons (.arg (.tail .head)) (.cons (.arg .head) .nil)
  sigs := [decision, pair]
  body := body
  closed := by
    intro d
    rw [body_live d]
    cases h0 : d 0 <;> cases h1 : d 1 <;>
      simp [required, h0, h1, List.mem_cons]

private def requested : Demand := fun p => p == 0
private def empty : Demand := fun _ => false

-- Payload is read on the recursive edge only when the callee's first result
-- is demanded. The non-tail primitive reads no data ports.
example : recursiveArm.liveIn requested = [.arg 1, .arg 2, .arg 3] := by decide
example : recursiveArm.liveIn empty = [.arg 1, .arg 2] := by decide
example : family.liveImports requested = [.arg 0] := by decide
example : Address.arg 3 ∈ (body.liveness requested).mayOut 0 :=
  (Code.mem_liveIn_iff body requested _).1 (by decide)

private def args (count payload spare : Nat) : Tuple machine.Val fn.args :=
  .cons (.data count) (two payload spare)

private theorem ready (cap : Nat) : family.Ready (one cap) := by
  refine ⟨rfl, ?_⟩
  intro params locals result
  refine ⟨?_, fun _ _ _ => trivial⟩
  intro i
  refine Fin.cases ?_ (fun _ => ?_) i
  · exact fun _ => trivial
  · exact ⟨⟨rfl, rfl⟩, fun _ _ => trivial⟩

private theorem agreed (cap n : Nat) :
    family.AgreesOnInputs requested (one cap) (one cap) (args n 41 4) (args n 41 40) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro ty p live
  cases p with
  | head => rfl
  | tail p =>
    cases p with
    | head => rfl
    | tail p =>
      cases p with
      | head => exact False.elim ((by decide : Address.arg 3 ∉ summary.live requested) live)
      | tail p => nomatch p

private def run (fuel cap count spare : Nat) :=
  family.run actions fuel 83 (one cap) (args count 41 spare) 20

private theorem related (fuel after cap count : Nat) :
    ∃ left right, run fuel cap count 4 = .ok left ∧ run fuel cap count 40 = .ok right ∧
      PrefixObservationsAgree actions requested after left right :=
  family.linked_prefixes_agree actions requested fuel after 83 (one cap) (one cap)
    (args count 41 4) (args count 41 40) 20 (ready cap) (ready cap) (agreed cap count)

private def returnedValues : Observation machine Nat pair → Option (Nat × Nat × Nat)
  | .returned (.cons (.data value) (.cons (.data spare) .nil)) store => some (value, spare, store)
  | _ => none

-- The recursive frame performs its post-call effect on return.
#guard (run 32 2 1 4).toOption.bind returnedValues == some (41, 4, 34)
#guard (run 32 2 1 40).toOption.bind returnedValues == some (41, 40, 34)

private def probeBlock (result : Except (Failure machine Nat) (Observation machine Nat pair)) : Bool :=
  match result with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, .cons (.data cap) .nil⟩, frames⟩ store) =>
    let input : Nat := cap
    input == 0 && store == 22 && Continuation.Descent.stackDepth frames == 4
  | _ => false

#guard probeBlock (run 32 0 1 4)
#guard probeBlock (run 32 0 1 40)

private def resume (result : Except (Failure machine Nat) (Observation machine Nat pair)) :
    Option (Observation machine Nat pair) :=
  match result with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, _⟩, frames⟩ _) =>
    some (observe actions (runFor actions 24 ⟨.returned .nil frames, 50⟩))
  | _ => none

#guard (resume (run 32 0 1 4)).bind returnedValues == some (41, 4, 60)
#guard (resume (run 32 0 1 40)).bind returnedValues == some (41, 40, 60)

private def repeated (spare store : Nat) (frame : Stack machine pair pair) : Config machine Nat pair :=
  ⟨.eval (family.invocation (one 2) (args 99 41 spare)) frame, store⟩

example (spare : Nat) :
    Executable.start actions 83 family.graph (one 2) .head (args 99 41 spare) 20 =
      .ok (repeated spare 20 .halt) := rfl

-- One full descent adds two frames and returns to the same actual φ dispatch.
private theorem descend (spare store : Nat) (frame : Stack machine pair pair) :
    ∃ deeper, runFor actions 8 (repeated spare store frame) = repeated spare (store + 1) deeper :=
  ⟨_, rfl⟩

private theorem keepsStepping (spare fuel : Nat) : ∀ (store : Nat) (frame : Stack machine pair pair),
    ∃ next, next? actions (runFor actions fuel (repeated spare store frame)) = some next := by
  induction fuel using Nat.strong_induction_on with
  | ind fuel ih =>
    intro store frame
    obtain ⟨deeper, reached⟩ := descend spare store frame
    by_cases enough : 8 ≤ fuel
    · rw [show fuel = 8 + (fuel - 8) by omega, runFor_add, reached]
      exact ih (fuel - 8) (by omega) (store + 1) deeper
    · cases stopped : next? actions (runFor actions fuel (repeated spare store frame)) with
      | some next => exact ⟨next, rfl⟩
      | none =>
        have fixed : runFor actions (8 - fuel) (runFor actions fuel (repeated spare store frame)) =
            runFor actions fuel (repeated spare store frame) := by
          cases 8 - fuel with
          | zero => rfl
          | succ n => simp only [runFor, stopped]
        rw [show 8 = fuel + (8 - fuel) by omega, runFor_add, fixed] at reached
        rw [reached] at stopped
        cases stopped

example (spare : Nat) : InfiniteTrace (Step actions.toPrimitives) (repeated spare 20 .halt) := by
  apply Continuation.Partial.Executable.infinite_iff_all_suspended.2
  intro fuel
  obtain ⟨next, step⟩ := keepsStepping spare fuel 20 .halt
  exact Continuation.Partial.Executable.observe_suspended.2 ⟨next, step_iff.2 step⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Singleton.Regression
