module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Thms
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Defs
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Wrapper.Thms
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Wrapper.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Synthesis.Thms
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Synthesis.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable.Thms
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Defs

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Regression

open NestedTheta.Liveness
open Ordered.Prefix (Plan Scope lastExport seededGraph)
open Continuation (Stack)
open Continuation.Partial (Config Step)
open Continuation.Partial.Executable (Actions Observation next? observe runFor runFor_add step_iff)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev single := [num]
private abbrev pair := [num, num]
private abbrev fn : Function Unit Unit := ⟨[num, num, num], pair⟩
private abbrev entry := [fn.port, fn.port, num, num, num, num]
private abbrev decision : List T := [.control 2, num]

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | route (first : Bool) : Op single decision
  | choose (extra cost : Nat) : Op single [.control (extra + 2)]
  | probe : Op single []
  | after : Op [] []

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .route _, .cons (.data count) .nil => .cons (.control 0) (.cons (.data count) .nil)
    | .choose _ _, _ => .cons (.control 0) .nil
    | .probe, _ => .nil
    | .after, _ => .nil

private def one (n : Nat) : Tuple machine.Val single := .cons (.data n) .nil
private def two (a b : Nat) : Tuple machine.Val pair := .cons (.data a) (one b)

private def actions : Actions machine Nat where
  step
    | .route first, .cons (.data count) .nil => fun store =>
      let count : Nat := count
      let tag : Fin 2 := if count = 0 then 0 else 1
      let next := if count = 99 then count else count - 1
      some (.cons (.control tag) (one next), store + (if first then 1 else 2))
    | .choose extra cost, .cons (.data value) .nil => fun store =>
      let value : Nat := value
      let tag : Fin (extra + 2) := ⟨value % (extra + 2), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
      some (.cons (.control tag) .nil, store + cost)
    | .probe, .cons (.data cap) .nil => fun store =>
      let cap : Nat := cap
      if cap = 0 then none else some (.nil, store + cap)
    | .after, _ => fun store => some (.nil, store + 10)

private def required (first : Bool) (demand : Demand) : List Address :=
  [.arg 0, .arg 1] ++ (if demand 0 then [.arg (if first then 2 else 3)] else []) ++
    (if demand 1 then [.arg (if first then 3 else 2)] else [])

private abbrev summaries : MemberSummaries Unit Unit where
  members := [fn, fn]
  captures := fun _ => single
  live := Fin.cases (required true) (fun _ => required false)
  monotone := by
    intro i low high le
    refine Fin.cases ?_ (fun _ => ?_) i <;>
      change required _ low ⊆ required _ high <;> clear i
    all_goals
      have selected (p : Nat) (a : Address) :
          (if low p then [a] else []) ⊆ (if high p then [a] else []) := by
        intro b h
        by_cases active : low p = true
        · simpa only [ite_eq_left active, ite_eq_left (le p active)] using h
        · simp [active] at h
      intro a h
      simp only [required, List.mem_append] at h ⊢
      exact h.imp (fun h => h.imp id (fun h => selected 0 _ h)) (fun h => selected 1 _ h)

private def capture : Port entry num := .tail (.tail .head)
private def count : Port entry num := .tail (.tail (.tail .head))
private def payload : Port entry num := .tail (.tail (.tail (.tail .head)))
private def spare : Port entry num := .tail (.tail (.tail (.tail (.tail .head))))

private def baseArm (first : Bool) (relay : Bool := false) : Code Op entry [] [[]] pair true (some summaries) :=
  .primitive .probe (.cons (.arg capture) .nil)
    (.ret (if relay then
      .cons (.arg count) (.cons (.arg (if first then payload else count)) .nil)
      else if first then .cons (.arg payload) (.cons (.arg spare) .nil)
      else .cons (.arg spare) (.cons (.arg payload) .nil)))

-- The two members expose payload at different result ports.
private def afterCall (swap : Bool) : Code Op entry [pair] [[]] pair true (some summaries) :=
  .primitive .after .nil
    (.ret (if swap then
      .cons (.output (0 : Fin 2) (.tail .head)) (.cons (.output (0 : Fin 2) .head) .nil)
      else .cons (.output (0 : Fin 2) .head) (.cons (.output (0 : Fin 2) (.tail .head)) .nil)))

private def recursiveArm (first : Bool) (relay : Bool := false) : Code Op entry [] [pair, []] pair true (some summaries) :=
  let captured : Wires entry [] single := .cons (.arg capture) .nil
  let args : Wires entry [] fn.args := .cons (.arg count) (.cons (.arg payload) (.cons (.arg spare) .nil))
  if first then .familyCall (table := summaries) 1 (.tail .head) captured args (afterCall true)
  else .familyCall (table := summaries) 0 .head captured args (afterCall (!relay))

private def armSigs : Fin 2 → List (Ports T) := Fin.cases [[]] (fun _ => [pair, []])

private def arms (first relay : Bool) (i : Fin 2) : Code Op entry [] (armSigs i) pair true (some summaries) :=
  Fin.cases (motive := fun j => Code Op entry [] (armSigs j) pair true (some summaries))
    (baseArm first relay) (fun _ => recursiveArm first relay) i

private def body (first : Bool) (relay : Bool := false) : Code Op entry [] [decision, pair] pair true (some summaries) :=
  let captures : Wires entry [decision] entry :=
    .cons (.arg .head) (.cons (.arg (.tail .head))
      (.cons (.arg capture) (.cons (.output (0 : Fin 1) (.tail .head))
        (.cons (.arg payload) (.cons (.arg spare) .nil)))))
  .primitive (.route first) (.cons (.arg count) .nil)
    (.gamma 0 armSigs (.output (0 : Fin 1) .head) captures (arms first relay)
      (.ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))))

private theorem body_live (first : Bool) (d : Demand) :
    ((body first).plan d).live =
      [.arg 3, .arg 2] ++ (if (if first then d 0 else d 1) then [.arg 4] else []) ++
        (if (if first then d 1 else d 0) then [.arg 5] else []) := by
  cases first <;> cases h0 : d 0 <;> cases h1 : d 1 <;>
    simp (config := { decide := true }) [body, arms, armSigs, baseArm, recursiveArm, afterCall, capture, count, payload,
      spare, summaries, Code.plan, DemandPlan.prepend, transfer, selectWires,
      Demand.observes, NestedTheta.Kind.demandReads, Wires.addresses, Origin.address, Port.index, definedAt,
      h0, h1]

private theorem closedBody (first : Bool) (d : Demand) :
    (∀ p, p < 2 → .arg p ∉ ((body first).plan d).live) ∧
    ∀ p, .arg (2 + p) ∈ ((body first).plan d).live → .arg p ∈ required first d := by
  rw [body_live first d]
  cases first <;> cases h0 : d 0 <;> cases h1 : d 1 <;>
    simp [required, h0, h1, List.mem_cons] <;>
      exact ⟨by intro p hp; omega, by intro p hp; omega⟩

private def template (relay : Bool) : Family.Template Op summaries single where
  context := single
  captures := .cons (.arg .head) .nil
  memberWires := Fin.cases
    (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) (.cons (.arg .head) .nil)))
    (Fin.cases (.cons (.output (0 : Fin 1) .head)
      (.cons (.arg (.tail (.tail .head))) (.cons (.arg .head) .nil))) (fun j => j.elim0))
  sigs := fun _ => [decision, pair]
  body := Fin.cases (body true relay) (Fin.cases (body false relay) (fun j => j.elim0))

private def family : Family Op summaries single where
  context := (template false).context
  captures := (template false).captures
  memberWires := (template false).memberWires
  sigs := (template false).sigs
  body := (template false).body
  closed := by
    intro i d
    refine Fin.cases (closedBody true d) (fun j => ?_) i
    obtain rfl := Fin.eq_zero j
    exact closedBody false d

private def requested : Demand := fun p => p == 0
private def requestedSecond : Demand := fun p => p == 1
private def empty : Demand := fun _ => false

-- Both edges require payload only through the demanded callee result.
example : (recursiveArm true).liveIn requested = [.arg 2, .arg 3, .arg 4] := by decide
example : (recursiveArm false).liveIn requestedSecond = [.arg 2, .arg 3, .arg 4] := by decide
example : (recursiveArm true).liveIn empty = [.arg 2, .arg 3] := by decide
example : (recursiveArm false).liveIn empty = [.arg 2, .arg 3] := by decide
example : Address.arg 4 ∈ ((body true).liveness requested).mayOut 0 :=
  (Code.mem_liveIn_iff (body true) requested _).1 (by decide)

private def args (count payload spare : Nat) : Tuple machine.Val fn.args :=
  .cons (.data count) (two payload spare)

private theorem ready (cap : Nat) : family.Ready (m := machine) (one cap) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · refine ⟨rfl, fun params _ _ => ⟨?_, fun _ _ _ => trivial⟩⟩
    intro arm
    refine Fin.cases ?_ (fun _ => ?_) arm
    · exact fun _ => trivial
    · exact ⟨⟨rfl, rfl⟩, fun _ _ => trivial⟩
  · obtain rfl := Fin.eq_zero j
    refine ⟨rfl, fun params _ _ => ⟨?_, fun _ _ _ => trivial⟩⟩
    intro arm
    refine Fin.cases ?_ (fun _ => ?_) arm
    · exact fun _ => trivial
    · exact ⟨⟨rfl, rfl⟩, fun _ _ => trivial⟩

private theorem agreed (cap n : Nat) :
    family.AgreesOnInputs 0 requested (one cap) (one cap) (args n 41 4) (args n 41 40) := by
  intro ty p live
  cases p with
  | head => rfl
  | tail p =>
    cases p with
    | head => rfl
    | tail p =>
      cases p with
      | head => rfl
      | tail p =>
        cases p with
        | head => exact False.elim ((by decide : Address.arg 3 ∉ required true requested) live)
        | tail p => nomatch p

private def run (fuel cap count spare : Nat) :=
  family.run 0 actions fuel 83 (one cap) (args count 41 spare) 20

example (fuel after cap count : Nat) :
    ∃ left right, run fuel cap count 4 = .ok left ∧ run fuel cap count 40 = .ok right ∧
      PrefixObservationsAgree actions requested after left right :=
  family.linked_prefixes_agree 0 actions requested fuel after 83 (one cap) (one cap)
    (args count 41 4) (args count 41 40) 20 (ready cap) (ready cap) (agreed cap count)

private def returnedValues : Observation machine Nat pair → Option (Nat × Nat × Nat)
  | .returned (.cons (.data value) (.cons (.data spare) .nil)) store => some (value, spare, store)
  | _ => none

-- The recursive frame performs its post-call effect on return.
#guard (run 64 2 2 4).toOption.bind returnedValues == some (41, 4, 46)
#guard (run 64 2 2 40).toOption.bind returnedValues == some (41, 40, 46)

private def probeBlock {outs : Ports T} (result : Except (Failure machine Nat) (Observation machine Nat outs))
    (depth : Nat := 6) : Bool :=
  match result with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, .cons (.data cap) .nil⟩, frames⟩ store) =>
    let input : Nat := cap
    input == 0 && store == 24 && Continuation.Descent.stackDepth frames == depth
  | _ => false

#guard probeBlock (run 64 0 2 4)
#guard probeBlock (run 64 0 2 40)

private def resume {outs : Ports T} (result : Except (Failure machine Nat) (Observation machine Nat outs)) :
    Option (Observation machine Nat outs) :=
  match result with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, _⟩, frames⟩ _) =>
    some (observe actions (runFor actions 40 ⟨.returned .nil frames, 50⟩))
  | _ => none

#guard (resume (run 64 0 2 4)).bind returnedValues == some (41, 4, 70)
#guard (resume (run 64 0 2 40)).bind returnedValues == some (41, 40, 70)

private def repeated (spare store : Nat) (frame : Stack machine pair pair) : Config machine Nat pair :=
  ⟨.eval (family.invocation 0 (one 2) (args 99 41 spare)) frame, store⟩

example (spare : Nat) :
    Executable.start actions 83 (family.graph 0) (one 2) .head (args 99 41 spare) 20 =
      .ok (repeated spare 20 .halt) := rfl

-- Two actual call edges add frames and return to the first member.
private def repeatedSecond (spare store : Nat) (frame : Stack machine pair pair) : Config machine Nat pair :=
  ⟨.eval (family.invocation 1 (one 2) (args 99 41 spare)) frame, store⟩

set_option maxHeartbeats 600000 in
private theorem descend (spare store : Nat) (frame : Stack machine pair pair) :
    ∃ deeper, runFor actions 16 (repeated spare store frame) = repeated spare (store + 3) deeper := by
  have first : ∃ next, runFor actions 8 (repeated spare store frame) = repeatedSecond spare (store + 1) next :=
    ⟨_, rfl⟩
  have second (next : Stack machine pair pair) :
      ∃ deeper, runFor actions 8 (repeatedSecond spare (store + 1) next) = repeated spare (store + 3) deeper :=
    ⟨_, rfl⟩
  obtain ⟨next, entered⟩ := first
  rw [show 16 = 8 + 8 by rfl, runFor_add, entered]
  exact second next

private theorem keepsStepping (spare fuel : Nat) : ∀ (store : Nat) (frame : Stack machine pair pair),
    ∃ next, next? actions (runFor actions fuel (repeated spare store frame)) = some next := by
  induction fuel using Nat.strong_induction_on with
  | ind fuel ih =>
    intro store frame
    obtain ⟨deeper, reached⟩ := descend spare store frame
    by_cases enough : 16 ≤ fuel
    · rw [show fuel = 16 + (fuel - 16) by omega, runFor_add, reached]
      exact ih (fuel - 16) (by omega) (store + 3) deeper
    · cases stopped : next? actions (runFor actions fuel (repeated spare store frame)) with
      | some next => exact ⟨next, rfl⟩
      | none =>
        have fixed : runFor actions (16 - fuel) (runFor actions fuel (repeated spare store frame)) =
            runFor actions fuel (repeated spare store frame) := by
          cases 16 - fuel with
          | zero => rfl
          | succ n => simp only [runFor, stopped]
        rw [show 16 = fuel + (16 - fuel) by omega, runFor_add, fixed] at reached
        rw [reached] at stopped
        cases stopped

example (spare : Nat) : InfiniteTrace (Step actions.toPrimitives) (repeated spare 20 .halt) := by
  apply Continuation.Partial.Executable.infinite_iff_all_suspended.2
  intro fuel
  obtain ⟨next, step⟩ := keepsStepping spare fuel 20 .halt
  exact Continuation.Partial.Executable.observe_suspended.2 ⟨next, step_iff.2 step⟩

-- Here A's first exit reads B's second, and B's second reads A's second.
-- Only A's second result has a direct use of the payload at the base case.
private def afterRounds (n : Nat) : Family.Rows summaries :=
  (Family.Template.round (template true))^[n] ∅

private def needsPayload (rows : Family.Rows summaries) (member : Fin 2) (demand : Demand) : Bool :=
  (Family.inputAddresses (Family.row summaries rows member (Family.demandMask demand))).contains (.arg 2)

#guard needsPayload (afterRounds 1) 0 requestedSecond
#guard !(needsPayload (afterRounds 1) 1 requestedSecond)
#guard needsPayload (afterRounds 2) 1 requestedSecond
#guard !(needsPayload (afterRounds 2) 0 requested)
#guard needsPayload (afterRounds 3) 0 requested
#guard (template true).summaries.live (0 : Fin 2) requested == [.arg 0, .arg 1, .arg 2]
#guard (template true).summaries.live (1 : Fin 2) requestedSecond == [.arg 0, .arg 1, .arg 2]
#guard (template true).summaries.live (0 : Fin 2) (fun _ => true) == [.arg 0, .arg 1, .arg 2]

private theorem relaySafe : (template true).ReferenceSafe := by
  unfold Family.Template.ReferenceSafe
  decide

private def inferred := (template true).admit relaySafe

private theorem relayReady (cap : Nat) : inferred.Ready (m := machine) (one cap) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · refine ⟨rfl, fun params _ _ => ⟨?_, fun _ _ _ => trivial⟩⟩
    intro arm
    refine Fin.cases ?_ (fun _ => ?_) arm
    · exact fun _ => trivial
    · exact ⟨⟨rfl, rfl⟩, fun _ _ => trivial⟩
  · obtain rfl := Fin.eq_zero j
    refine ⟨rfl, fun params _ _ => ⟨?_, fun _ _ _ => trivial⟩⟩
    intro arm
    refine Fin.cases ?_ (fun _ => ?_) arm
    · exact fun _ => trivial
    · exact ⟨⟨rfl, rfl⟩, fun _ _ => trivial⟩

private theorem relayLive :
    (template true).summaries.live (0 : Fin 2) requested = [.arg 0, .arg 1, .arg 2] := by decide

private theorem relayAgreed (cap count : Nat) :
    inferred.AgreesOnInputs (0 : Fin 2) requested (one cap) (one cap) (args count 41 4) (args count 41 40) := by
  intro ty p live
  cases p with
  | head => rfl
  | tail p =>
    cases p with
    | head => rfl
    | tail p =>
      cases p with
      | head => rfl
      | tail p =>
        cases p with
        | head => exact False.elim ((by rw [relayLive]; decide :
          Address.arg 3 ∉ (template true).summaries.live (0 : Fin 2) requested) live)
        | tail p => nomatch p

private def runInferred (fuel cap count spare : Nat) :=
  inferred.run (0 : Fin 2) actions fuel 83 (one cap) (args count 41 spare) 20

example (fuel after cap count : Nat) :
    ∃ left right, runInferred fuel cap count 4 = .ok left ∧ runInferred fuel cap count 40 = .ok right ∧
      PrefixObservationsAgree actions requested after left right :=
  (template true).linked_prefixes_agree relaySafe (0 : Fin 2) actions requested fuel after 83 (one cap) (one cap)
    (args count 41 4) (args count 41 40) 20 (relayReady cap) (relayReady cap) (relayAgreed cap count)

#guard (runInferred 64 2 2 4).toOption.bind returnedValues == some (41, 0, 46)
#guard (runInferred 64 2 2 40).toOption.bind returnedValues == some (41, 0, 46)
#guard probeBlock (runInferred 64 0 2 4)
#guard probeBlock (runInferred 64 0 2 40)
#guard (resume (runInferred 64 0 2 4)).bind returnedValues == some (41, 0, 70)
#guard (resume (runInferred 64 0 2 40)).bind returnedValues == some (41, 0, 70)

-- The λ reads a member of the earlier φ binding. Its result wire reads the
-- callee's first result after a separate non-tail store effect.
private abbrev exportFn : Function Unit Unit := ⟨fn.args, single⟩

private abbrev wrapperEntry := fn.port :: (single ++ fn.args)

private def wrapperSuffix :
    Code Op wrapperEntry [pair] [[]] single true (some (template true).summaries) :=
  .primitive .after .nil (.ret (.cons (.output (0 : Fin 2) .head) .nil))

private def wrapper : Family.Wrapper inferred exportFn where
  member := (0 : Fin 2)
  context := single
  captures := .cons (.arg .head) .nil
  sigs := [pair, []]
  body := .familyCall (table := (template true).summaries) (0 : Fin 2) .head
    (.cons (.arg (.tail .head)) .nil)
    (.cons (.arg (.tail (.tail .head)))
      (.cons (.arg (.tail (.tail (.tail .head))))
        (.cons (.arg (.tail (.tail (.tail (.tail .head))))) .nil)))
    wrapperSuffix

example : wrapper.dispatchOrigin.address = .output 0 0 := rfl

private theorem wrapperReads : (wrapper.body.plan requested).live = [.arg 1, .arg 2, .arg 3] := by
  have usesFirst : resultDemand 0 (wrapperSuffix.plan requested) = requested := by
    funext p
    cases p <;> rfl
  change ((wrapperSuffix.plan requested).prepend 0
    (applyReads ((template true).summaries.live (0 : Fin 2) (resultDemand 0 (wrapperSuffix.plan requested)))
      _ _)).live = _
  rw [usesFirst, relayLive]
  decide

private theorem wrapperLive : wrapper.liveIn requested = [.arg 1, .arg 2, .arg 3] := by
  simp only [Family.Wrapper.liveIn, Code.liveIn, wrapperReads]
  decide

#guard wrapper.liveIn empty == [.arg 1, .arg 2]
example : Address.arg 3 ∈ (wrapper.body.liveness requested).mayOut 0 :=
  (wrapper.mem_liveIn_iff requested _).1 (by rw [wrapperLive]; decide)

private theorem wrapperReady (cap count spare : Nat) : wrapper.Ready (one cap) (args count 41 spare) :=
  ⟨relayReady cap, fun _ => ⟨⟨rfl, rfl⟩, fun _ _ => trivial⟩⟩

private theorem wrapperAgreed (cap count : Nat) :
    wrapper.AgreesOnInputs requested (one cap) (one cap) (args count 41 4) (args count 41 40) := by
  intro ty p live
  cases p with
  | head => exact False.elim ((by rw [wrapperLive]; decide : Address.arg 0 ∉ wrapper.liveIn requested) live)
  | tail p =>
    cases p with
    | head => rfl
    | tail p =>
      cases p with
      | head => rfl
      | tail p =>
        cases p with
        | head => rfl
        | tail p =>
          cases p with
          | head => exact False.elim ((by rw [wrapperLive]; decide : Address.arg 4 ∉ wrapper.liveIn requested) live)
          | tail p => nomatch p

private def runWrapper (fuel cap count spare : Nat) :=
  wrapper.run actions fuel 83 (one cap) (args count 41 spare) 20

example (fuel after cap count : Nat) :
    ∃ left right, runWrapper fuel cap count 4 = .ok left ∧ runWrapper fuel cap count 40 = .ok right ∧
      PrefixObservationsAgree actions requested after left right :=
  wrapper.linked_prefixes_agree actions requested fuel after 83 (one cap) (one cap)
    (args count 41 4) (args count 41 40) 20
    (wrapperReady cap count 4) (wrapperReady cap count 40) (wrapperAgreed cap count)

private def wrapperResult : Observation machine Nat single → Option (Nat × Nat)
  | .returned (.cons (.data value) .nil) store => some (value, store)
  | _ => none

#guard (runWrapper 64 2 2 4).toOption.bind wrapperResult == some (41, 56)
#guard (runWrapper 64 2 2 40).toOption.bind wrapperResult == some (41, 56)
#guard probeBlock (runWrapper 64 0 2 4) 7
#guard probeBlock (runWrapper 64 0 2 40) 7
#guard (resume (runWrapper 64 0 2 4)).bind wrapperResult == some (41, 80)
#guard (resume (runWrapper 64 0 2 40)).bind wrapperResult == some (41, 80)

-- The later λ captures the earlier λ at vertex 1 and the φ member at
-- vertex 0. The latter is an actual witness for the earlier λ's capture.
private abbrev seeds := (template true).summaries
private abbrev seedSigs := [memberPorts seeds.members]
private abbrev firstSigs := seedSigs ++ [[exportFn.port]]

private def firstBinding : Ordered.Binding Op seeds single seedSigs exportFn where
  context := wrapper.lambda.context
  captures := wrapper.lambda.captures
  sigs := wrapper.sigs
  body := wrapper.body

private abbrev firstSlots := Ordered.prepend firstBinding.summary seeds
private abbrev laterEntry := [exportFn.port, fn.port, num] ++ exportFn.args

private def laterSuffix : Code Op laterEntry [single] [[]] single true (some firstSlots) :=
  .primitive .after .nil (.ret (.cons (.output (0 : Fin 2) .head) .nil))

private def laterBinding : Ordered.Binding Op firstSlots single firstSigs exportFn where
  context := [exportFn.port, fn.port, num]
  captures := .cons (.output (1 : Fin 2) .head)
    (.cons (.output (0 : Fin 2) .head) (.cons (.arg .head) .nil))
  sigs := [single, []]
  body := .familyCall (table := firstSlots) (0 : Fin 3) .head
    (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))
    (.cons (.arg (.tail (.tail (.tail .head))))
      (.cons (.arg (.tail (.tail (.tail (.tail .head)))))
        (.cons (.arg (.tail (.tail (.tail (.tail (.tail .head)))))) .nil)))
    laterSuffix

private def orderedLambdas : ModuleTerm Op single seedSigs [[exportFn.port], [exportFn.port]] [exportFn.port] :=
  .bind (.lambda firstBinding.term)
    (.bind (.lambda laterBinding.term) (.ret (lastExport firstSigs exportFn)))

private def orderedGraph := seededGraph inferred orderedLambdas

private def firstScope (cap : Nat) :=
  (Scope.seed inferred (one cap) (one cap)).add firstBinding (one cap) (one cap)

private def orderedPlan (cap : Nat) :
    Plan (one cap) (one cap) (Scope.seed inferred (one cap) (one cap)) laterBinding.summary orderedLambdas :=
  Plan.lambdaDirect (scope := Scope.seed inferred (one cap) (one cap)) firstBinding
    (Plan.finishDirect (scope := firstScope cap) laterBinding)

private def admitted (cap : Nat) :=
  (orderedPlan cap).admit inferred actions 83 (one cap) (one cap) 20 (relayReady cap) (relayReady cap)

private def checkedExport (cap : Nat) := (admitted cap).get (by rfl)

private theorem laterReads : laterBinding.summary.live requested = [.arg 2, .arg 3, .arg 4] := by
  have usesFirst : resultDemand 0 (laterSuffix.plan requested) = requested := by
    funext p
    cases p <;> rfl
  change ((laterSuffix.plan requested).prepend 0
    (applyReads (firstBinding.summary.live (resultDemand 0 (laterSuffix.plan requested))) _ _)).live = _
  rw [usesFirst]
  have firstReads : firstBinding.summary.live requested = [.arg 1, .arg 2, .arg 3] := wrapperReads
  rw [firstReads]
  decide

#guard laterBinding.summary.live empty == [.arg 2, .arg 3]
example : Address.arg 4 ∈ (laterBinding.body.liveness requested).mayOut 0 :=
  (laterBinding.body.mem_liveIn_iff requested _).1 (by
    simp only [Code.liveIn, List.mem_eraseDups]
    change Address.arg 4 ∈ laterBinding.summary.live requested
    rw [laterReads]
    decide)

private theorem laterAgreed (cap count : Nat) :
    Ordered.InputsAgree (m := machine) laterBinding.summary requested
      (prependContext (args count 41 4) (checkedExport cap).capsL)
      (prependContext (args count 41 40) (checkedExport cap).capsR) := by
  intro ty p live
  change .arg p.index ∈ laterBinding.summary.live requested at live
  rw [laterReads] at live
  cases p with
  | head => simp [Port.index] at live
  | tail p =>
    cases p with
    | head => simp [Port.index] at live
    | tail p =>
      cases p with
      | head => rfl
      | tail p =>
        cases p with
        | head => rfl
        | tail p =>
          cases p with
          | head => rfl
          | tail p =>
            cases p with
            | head => simp [Port.index] at live
            | tail p => nomatch p

private def runOrdered (fuel cap count spare : Nat) :=
  Executable.run actions fuel 83 orderedGraph (one cap) .head (args count 41 spare) 20

example (fuel after cap count : Nat) :
    ∃ left right, runOrdered fuel cap count 4 = .ok left ∧ runOrdered fuel cap count 40 = .ok right ∧
      PrefixObservationsAgree actions requested after left right :=
  Ordered.Prefix.Export.linked_prefixes_agree (actions := actions) (summary := laterBinding.summary)
    requested fuel after 83 orderedGraph (one cap) (one cap) (args count 41 4) (args count 41 40) 20
    (checkedExport cap) (laterAgreed cap count)

#guard (runOrdered 80 2 2 4).toOption.bind wrapperResult == some (41, 66)
#guard (runOrdered 80 2 2 40).toOption.bind wrapperResult == some (41, 66)
#guard probeBlock (runOrdered 80 0 2 4) 8
#guard probeBlock (runOrdered 80 0 2 40) 8
#guard (resume (runOrdered 80 0 2 4)).bind wrapperResult == some (41, 90)
#guard (resume (runOrdered 80 0 2 40)).bind wrapperResult == some (41, 90)

-- This skipped λ has the same signature and builds the same closure as
-- the first one. Its linker position nevertheless carries no admission.
private def uncheckedLambda : LambdaTerm Op single firstSigs exportFn :=
  ⟨firstBinding.context, .cons (.output (0 : Fin 2) .head) (.cons (.arg .head) .nil),
    firstBinding.sigs, firstBinding.body.term⟩

private abbrev skippedSigs := firstSigs ++ [[exportFn.port]]

private def rejectedBinding : Ordered.Binding Op firstSlots single skippedSigs exportFn where
  context := laterBinding.context
  captures := .cons (.output (2 : Fin 3) .head)
    (.cons (.output (0 : Fin 3) .head) (.cons (.arg .head) .nil))
  sigs := laterBinding.sigs
  body := laterBinding.body

private def rejectedLambdas :
    ModuleTerm Op single seedSigs [[exportFn.port], [exportFn.port], [exportFn.port]] [exportFn.port] :=
  .bind (.lambda firstBinding.term) (.bind (.lambda uncheckedLambda)
    (.bind (.lambda rejectedBinding.term) (.ret (lastExport skippedSigs exportFn))))

private def rejectedPlan (cap : Nat) :
    Plan (one cap) (one cap) (Scope.seed inferred (one cap) (one cap)) rejectedBinding.summary rejectedLambdas :=
  Plan.lambdaDirect (scope := Scope.seed inferred (one cap) (one cap)) firstBinding
    (Plan.skipLambda (scope := firstScope cap) uncheckedLambda
      (Plan.finishDirect (scope := (firstScope cap).skip uncheckedLambda (one cap) (one cap)) rejectedBinding))

example (cap : Nat) :
    (rejectedPlan cap).admit inferred actions 83 (one cap) (one cap) 20 (relayReady cap) (relayReady cap) = none :=
  rfl

#guard (Executable.run actions 80 83 (seededGraph inferred rejectedLambdas) (one 2) .head (args 2 41 4) 20
  |>.toOption.bind wrapperResult) == some (41, 66)

-- The site still names an earlier slot, but its target operand is one
-- of the caller's formal arguments rather than a captured linker source.
private abbrev formalFn : Function Unit Unit := ⟨exportFn.port :: exportFn.args, single⟩

private def formalBinding : Ordered.Binding Op firstSlots single firstSigs formalFn where
  context := [fn.port, num]
  captures := .cons (.output (0 : Fin 2) .head) (.cons (.arg .head) .nil)
  sigs := [single]
  body := .familyCall (table := firstSlots) (0 : Fin 3) (.tail (.tail .head))
    (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.cons (.arg (.tail (.tail (.tail .head))))
      (.cons (.arg (.tail (.tail (.tail (.tail .head)))))
        (.cons (.arg (.tail (.tail (.tail (.tail (.tail .head)))))) .nil)))
    (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def formalLambdas : ModuleTerm Op single seedSigs [[exportFn.port], [formalFn.port]] [formalFn.port] :=
  .bind (.lambda firstBinding.term)
    (.bind (.lambda formalBinding.term) (.ret (lastExport firstSigs formalFn)))

private def formalPlan (cap : Nat) :
    Plan (one cap) (one cap) (Scope.seed inferred (one cap) (one cap)) formalBinding.summary formalLambdas :=
  Plan.lambdaDirect (scope := Scope.seed inferred (one cap) (one cap)) firstBinding
    (Plan.finishDirect (scope := firstScope cap) formalBinding)

example (cap : Nat) :
    (formalPlan cap).admit inferred actions 83 (one cap) (one cap) 20 (relayReady cap) (relayReady cap) = none :=
  rfl

-- A ternary γ forwards the captures into its first arm. A binary γ
-- in that arm permutes those wires again before selecting a callee.
private abbrev gammaContext := [exportFn.port, fn.port, fn.port, num]
private abbrev gammaEntry := gammaContext ++ exportFn.args
private abbrev gammaChild := [fn.port, exportFn.port, num, fn.port, num, num, num]
private abbrev innerChild := [num, fn.port, fn.port, exportFn.port, num, num, num]

private def gammaWires : Wires gammaEntry [[.control 3]] gammaChild :=
  .cons (.arg (.tail .head))
    (.cons (.arg .head)
      (.cons (.arg (.tail (.tail (.tail .head))))
        (.cons (.arg (.tail (.tail .head)))
          (.cons (.arg (.tail (.tail (.tail (.tail .head)))))
            (.cons (.arg (.tail (.tail (.tail (.tail (.tail .head))))))
              (.cons (.arg (.tail (.tail (.tail (.tail (.tail (.tail .head))))))) .nil))))))

private def innerWires (mismatch : Bool) : Wires gammaChild [[.control 2]] innerChild :=
  .cons (.arg (.tail (.tail .head)))
    (.cons (.arg .head)
      (.cons (.arg (if mismatch then .head else .tail (.tail (.tail .head))))
        (.cons (.arg (.tail .head))
          (.cons (.arg (.tail (.tail (.tail (.tail (.tail .head))))))
            (.cons (.arg (.tail (.tail (.tail (.tail .head)))))
              (.cons (.arg (.tail (.tail (.tail (.tail (.tail (.tail .head))))))) .nil))))))

private def gammaArguments : Wires gammaChild [] exportFn.args :=
  .cons (.arg (.tail (.tail (.tail (.tail .head)))))
    (.cons (.arg (.tail (.tail (.tail (.tail (.tail .head))))))
      (.cons (.arg (.tail (.tail (.tail (.tail (.tail (.tail .head))))))) .nil))

private def innerArguments : Wires innerChild [] exportFn.args :=
  .cons (.arg (.tail (.tail (.tail (.tail (.tail .head))))))
    (.cons (.arg (.tail (.tail (.tail (.tail .head)))))
      (.cons (.arg (.tail (.tail (.tail (.tail (.tail (.tail .head))))))) .nil))

private def innerSigs : Fin 2 → List (Ports T) := Fin.cases [single] (fun _ => [pair])

private def innerArms (i : Fin 2) : Code Op innerChild [] (innerSigs i) single true (some firstSlots) :=
  Fin.cases (motive := fun i => Code Op innerChild [] (innerSigs i) single true (some firstSlots))
    (.familyCall (table := firstSlots) (0 : Fin 3) (.tail (.tail (.tail .head)))
      (.cons (.arg (.tail .head)) (.cons (.arg .head) .nil)) innerArguments
      (.ret (.cons (.output (0 : Fin 1) .head) .nil)))
    (fun _ => .familyCall (table := firstSlots) (2 : Fin 3) (.tail (.tail .head))
      (.cons (.arg .head) .nil) innerArguments
      (.ret (.cons (.output (0 : Fin 1) (.tail .head)) .nil))) i

private abbrev nestedSigs : List (Ports T) := [[.control 2], single, []]
private def gammaArmSigs : Fin 3 → List (Ports T) := Fin.cases nestedSigs (Fin.cases [pair] (fun _ => []))

private def gammaArms (mismatch : Bool) (i : Fin 3) : Code Op gammaChild [] (gammaArmSigs i) single true (some firstSlots) :=
  Fin.cases (motive := fun i => Code Op gammaChild [] (gammaArmSigs i) single true (some firstSlots))
    (.primitive (.choose 0 0) (.cons (.arg (.tail (.tail (.tail (.tail .head))))) .nil)
      (.gamma 0 innerSigs (.output (0 : Fin 1) .head) (innerWires mismatch) innerArms
        (.primitive .after .nil (.ret (.cons (.output (1 : Fin 3) .head) .nil)))))
    (Fin.cases
      (.familyCall (table := firstSlots) (2 : Fin 3) (.tail (.tail (.tail .head)))
        (.cons (.arg (.tail (.tail .head))) .nil) gammaArguments
        (.ret (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))
      (fun _ => .ret (.cons (.arg (.tail (.tail (.tail (.tail (.tail .head)))))) .nil))) i

private def gammaBinding (mismatch : Bool) : Ordered.Binding Op firstSlots single firstSigs exportFn where
  context := gammaContext
  captures := .cons (.output (1 : Fin 2) .head)
    (.cons (.output (0 : Fin 2) .head)
      (.cons (.output (0 : Fin 2) (.tail .head)) (.cons (.arg .head) .nil)))
  sigs := [[.control 3], single, []]
  body := .primitive (.choose 1 2) (.cons (.arg (.tail (.tail (.tail (.tail .head))))) .nil)
    (.gamma 1 gammaArmSigs (.output (0 : Fin 1) .head) gammaWires (gammaArms mismatch)
      (.primitive .after .nil (.ret (.cons (.output (1 : Fin 3) .head) .nil))))

private def gammaLambdas (mismatch : Bool) :
    ModuleTerm Op single seedSigs [[exportFn.port], [exportFn.port]] [exportFn.port] :=
  .bind (.lambda firstBinding.term)
    (.bind (.lambda (gammaBinding mismatch).term) (.ret (lastExport firstSigs exportFn)))

private def gammaPlan (cap : Nat) (mismatch : Bool) :
    Plan (one cap) (one cap) (Scope.seed inferred (one cap) (one cap))
      (gammaBinding mismatch).summary (gammaLambdas mismatch) :=
  Plan.lambdaDirect (scope := Scope.seed inferred (one cap) (one cap)) firstBinding
    (Plan.finishDirect (scope := firstScope cap) (gammaBinding mismatch))

private def gammaAdmitted (cap : Nat) (mismatch : Bool) :=
  (gammaPlan cap mismatch).admit inferred actions 83 (one cap) (one cap) 20 (relayReady cap) (relayReady cap)

private def gammaExport (cap : Nat) := (gammaAdmitted cap false).get (by rfl)

-- Substitute the other same-signature φ at the second inner arm's
-- target. The checker rejects the plan even if the first inner arm runs.
example (cap : Nat) : gammaAdmitted cap true = none := rfl

private theorem gammaSpareDead : Address.arg 6 ∉ (gammaBinding false).summary.live requested := by decide

#guard ((gammaBinding false).summary.live requested).contains (.arg 4)
#guard ((gammaBinding false).summary.live requested).contains (.arg 5)

private theorem gammaAgreed (cap count : Nat) :
    Ordered.InputsAgree (m := machine) (gammaBinding false).summary requested
      (prependContext (args count 41 4) (gammaExport cap).capsL)
      (prependContext (args count 41 40) (gammaExport cap).capsR) := by
  intro ty p live
  let captured := (gammaBinding false).captures.read (one cap) (firstScope cap).localsL
  change (prependContext (args count 41 4) captured).get p = (prependContext (args count 41 40) captured).get p
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · rfl
  cases p with
  | head => exact False.elim (gammaSpareDead live)
  | tail p => nomatch p

private def runGamma (mismatch : Bool) (fuel cap count spare : Nat) :=
  Executable.run actions fuel 83 (seededGraph inferred (gammaLambdas mismatch)) (one cap) .head (args count 41 spare) 20

example (fuel after cap count : Nat) :
    ∃ left right, runGamma false fuel cap count 4 = .ok left ∧ runGamma false fuel cap count 40 = .ok right ∧
      PrefixObservationsAgree actions requested after left right :=
  Ordered.Prefix.Export.linked_prefixes_agree (actions := actions) (summary := (gammaBinding false).summary)
    requested fuel after 83 (seededGraph inferred (gammaLambdas false)) (one cap) (one cap)
    (args count 41 4) (args count 41 40) 20 (gammaExport cap) (gammaAgreed cap count)

#guard (runGamma false 80 2 0 4).toOption.bind wrapperResult == some (0, 55)
#guard (runGamma false 80 2 0 40).toOption.bind wrapperResult == some (0, 55)
#guard (runGamma false 80 2 1 4).toOption.bind wrapperResult == some (41, 47)
#guard (runGamma false 80 2 1 40).toOption.bind wrapperResult == some (41, 47)
#guard (runGamma false 80 2 2 4).toOption.bind wrapperResult == some (41, 32)
#guard (runGamma false 160 2 3 4).toOption.bind wrapperResult == some (0, 80)
#guard (runGamma true 80 2 0 4).toOption.bind wrapperResult == some (0, 55)

private def gammaBlock (count : Nat) : Option (Nat × Nat) :=
  match runGamma false 80 0 count 4 with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, .cons (.data cap) .nil⟩, _⟩ store) => some (cap, store)
  | _ => none

#guard gammaBlock 0 == some (0, 23)
#guard gammaBlock 1 == some (0, 25)
#guard gammaBlock 3 == some (0, 28)
#guard (resume (runGamma false 80 0 0 4)).bind wrapperResult == some (0, 80)
#guard (resume (runGamma false 80 0 1 4)).bind wrapperResult == some (41, 70)
#guard (resume (runGamma false 80 0 3 4)).bind wrapperResult == some (0, 100)

-- The first θ activation only updates the counter. Its second activation
-- calls φ through the carried target and witnesses, then exits.
private abbrev thetaContext := [fn.port, fn.port, num]
private abbrev thetaCarried := thetaContext ++ exportFn.args

private def thetaA : Port thetaCarried fn.port := .head
private def thetaB : Port thetaCarried fn.port := .tail .head
private def thetaCapture : Port thetaCarried num := .tail (.tail .head)
private def thetaCount : Port thetaCarried num := .tail (.tail (.tail .head))
private def thetaPayload : Port thetaCarried num := .tail (.tail (.tail (.tail .head)))
private def thetaSpare : Port thetaCarried num := .tail (.tail (.tail (.tail (.tail .head))))

private def thetaArgs {past : List (Ports T)} : Wires thetaCarried past exportFn.args :=
  .cons (.arg thetaCount) (.cons (.arg thetaPayload) (.cons (.arg thetaSpare) .nil))

private def thetaWires {past : List (Ports T)} : Wires thetaCarried past thetaCarried :=
  .cons (.arg thetaA) (.cons (.arg thetaB) (.cons (.arg thetaCapture) thetaArgs))

private def thetaArmSigs : Fin 2 → List (Ports T) := Fin.cases [pair, []] (fun _ => [])

private def thetaArms (i : Fin 2) :
    Code Op thetaCarried [] (thetaArmSigs i) single true (some seeds) :=
  Fin.cases (motive := fun i => Code Op thetaCarried [] (thetaArmSigs i) single true (some seeds))
    (.familyCall (table := seeds) (0 : Fin 2) thetaA (.cons (.arg thetaCapture) .nil) thetaArgs
      (.primitive .after .nil (.ret (.cons (.output (0 : Fin 2) (.tail .head)) .nil))))
    (fun _ => .ret (.cons (.arg thetaPayload) .nil)) i

private def thetaBody (swap : Bool) :
    Code Op thetaCarried [] [decision, single] (Theta.BodyResults thetaCarried) true (some seeds) :=
  let next : Wires thetaCarried [decision, single] (Theta.BodyResults thetaCarried) :=
    .cons (.output (0 : Fin 2) .head)
      (.cons (.arg (if swap then thetaB else thetaA))
        (.cons (.arg (if swap then thetaA else thetaB))
          (.cons (.arg thetaCapture)
            (.cons (.output (0 : Fin 2) (.tail .head))
              (.cons (.output (1 : Fin 2) .head) (.cons (.arg thetaSpare) .nil))))))
  .primitive (.route true) (.cons (.arg thetaCount) .nil)
    (.gamma 0 thetaArmSigs (.output (0 : Fin 1) .head) thetaWires thetaArms (.ret next))

private def thetaBinding (swap : Bool) : Ordered.Binding Op seeds single seedSigs exportFn where
  context := thetaContext
  captures := .cons (.output (0 : Fin 1) .head)
    (.cons (.output (0 : Fin 1) (.tail .head)) (.cons (.arg .head) .nil))
  sigs := [thetaCarried, []]
  body := .theta thetaWires (thetaBody swap)
    (.primitive .after .nil (.ret (.cons (.output (0 : Fin 2) thetaPayload) .nil)))

private def thetaLambdas (swap : Bool) : ModuleTerm Op single seedSigs [[exportFn.port]] [exportFn.port] :=
  .bind (.lambda (thetaBinding swap).term) (.ret (lastExport seedSigs exportFn))

private def thetaPlan (cap : Nat) (swap : Bool) :
    Plan (one cap) (one cap) (Scope.seed inferred (one cap) (one cap))
      (thetaBinding swap).summary (thetaLambdas swap) :=
  Plan.finishDirect (scope := Scope.seed inferred (one cap) (one cap)) (thetaBinding swap)

-- Start at the numbered vertex table and export wire. The demand witness
-- must cover the source recovered from this table.
private def thetaNumbered (swap : Bool) : Omega Op single [exportFn.port] (seedSigs ++ [[exportFn.port]]) :=
  ⟨⟨Fin.cases (.phi inferred.group.toGraph)
      (Fin.cases (.lambda (thetaBinding swap).term.toGraph) (fun i => i.elim0)),
    lastExport seedSigs exportFn⟩⟩

private theorem thetaSource (swap : Bool) :
    (thetaNumbered swap).toTerm = ⟨.bind (.phi inferred.group) (thetaLambdas swap)⟩ := by
  change (seededGraph inferred (thetaLambdas swap)).toTerm = _
  exact OmegaTerm.toTerm_toGraph _

private def thetaAdmitted (cap : Nat) (swap : Bool) :=
  (thetaPlan cap swap).analyzeNumbered inferred actions 83 (thetaNumbered swap) (one cap) (one cap) 20
    (thetaSource swap) (relayReady cap) (relayReady cap)

private def thetaAnalysis (cap : Nat) := (thetaAdmitted cap false).get (by rfl)

-- The actual initial callable wires still match. Swapping the two carried
-- callables on the backedge removes the target's provenance at the call.
example (cap : Nat) : thetaAdmitted cap true = none := rfl

private def spareFormal : Port exportFn.args num := .tail (.tail .head)

#guard (thetaAnalysis 2).liveFormal requested (.head : Port exportFn.args num)
#guard (thetaAnalysis 2).liveFormal requested (.tail .head : Port exportFn.args num)
#guard !(thetaAnalysis 2).liveFormal requested spareFormal

set_option maxRecDepth 2048 in
example : Address.arg 3 ∈ ((thetaAnalysis 2).problem requested).mayOut 0 :=
  ((thetaAnalysis 2).mem_liveIn_iff requested _).1 (by decide)

private def runTheta (swap : Bool) (fuel cap count spare : Nat) :=
  Executable.run actions fuel 83 (thetaNumbered swap) (one cap) .head (args count 41 spare) 20

private def thetaSubstitutedFormals (cap count spare : Nat) : Tuple machine.Val exportFn.args :=
  (thetaAnalysis cap).substituteDeadFormals requested (args count 41 spare) (args 99 900 0)

-- The proposed counter and payload changes are discarded. The spare is replaced.
set_option maxRecDepth 2048 in
example : thetaSubstitutedFormals 2 1 40 = args 1 41 0 := rfl

private def runThetaSubstituted (fuel cap count spare : Nat) :=
  Executable.run actions fuel 83 (thetaNumbered false) (one cap) .head (thetaSubstitutedFormals cap count spare) 20

example (fuel after cap count spare : Nat) :
    ∃ left right, runTheta false fuel cap count spare = .ok left ∧
      runThetaSubstituted fuel cap count spare = .ok right ∧ PrefixObservationsAgree actions requested after left right :=
  (thetaAnalysis cap).linked_substituteDeadFormals requested fuel after (args count 41 spare) (args 99 900 0)
    (fun _ _ => rfl)

#guard (runTheta false 80 2 1 4).toOption.bind wrapperResult == some (41, 45)
#guard (runTheta false 80 2 1 40).toOption.bind wrapperResult == some (41, 45)
#guard (runTheta true 80 2 0 4).toOption.bind wrapperResult == some (41, 44)
#guard (runTheta true 80 2 1 4).toOption.bind wrapperResult == some (0, 46)

private def thetaBlock (run : Except (Failure machine Nat) (Observation machine Nat single)) : Option (Nat × Nat) :=
  match run with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, .cons (.data cap) .nil⟩, _⟩ store) => some (cap, store)
  | _ => none

#guard thetaBlock (runTheta false 80 0 0 4) == some (0, 22)
#guard thetaBlock (runTheta false 80 0 1 4) == some (0, 23)
#guard thetaBlock (runTheta false 80 0 1 40) == some (0, 23)
#guard (resume (runTheta false 80 0 1 4)).bind wrapperResult == some (41, 70)
#guard (resume (runTheta false 80 0 1 40)).bind wrapperResult == some (41, 70)

#guard (runThetaSubstituted 80 2 1 40).toOption.bind wrapperResult == some (41, 45)
#guard thetaBlock (runThetaSubstituted 80 0 1 40) == some (0, 23)
#guard (resume (runThetaSubstituted 80 0 1 40)).bind wrapperResult == some (41, 70)

-- Both arms can read different child ports and still forward the same
-- linker wires. The suffix reads the actual γ output ports.
private abbrev joinChild := [fn.port, num, fn.port, fn.port, num, num]
private abbrev joinPorts := [num, fn.port]

private def joinWires : Wires thetaCarried [decision] joinChild :=
  .cons (.arg thetaA) (.cons (.arg thetaCapture) (.cons (.arg thetaB)
    (.cons (.arg thetaA) (.cons (.arg thetaCapture) (.cons (.arg thetaCount) .nil)))))

private def joinArms (wrong : Bool) (i : Fin 2) : Code Op joinChild [] [[]] joinPorts true (some seeds) :=
  Fin.cases
    (.primitive .probe (.cons (.arg (.tail (.tail (.tail (.tail (.tail .head)))))) .nil)
      (.ret (.cons (.arg (.tail .head)) (.cons (.arg .head) .nil))))
    (fun _ => .primitive .after .nil
      (.ret (.cons (.arg (.tail (.tail (.tail (.tail .head)))))
        (.cons (.arg (if wrong then .tail (.tail .head) else .tail (.tail (.tail .head)))) .nil)))) i

private def joinBinding (wrong : Bool) : Ordered.Binding Op seeds single seedSigs exportFn where
  context := thetaContext
  captures := (thetaBinding false).captures
  sigs := [decision, joinPorts, pair, []]
  body := .primitive (.route true) (.cons (.arg thetaCount) .nil)
    (.gamma 0 (fun _ => [[]]) (.output (0 : Fin 1) .head) joinWires (joinArms wrong)
      (.callAt (table := seeds) (0 : Fin 2) (.output (1 : Fin 2) (.tail .head))
        (.cons (.output (1 : Fin 2) .head) .nil)
        (.cons (.output (0 : Fin 2) (.tail .head)) (.cons (.arg thetaPayload) (.cons (.arg thetaSpare) .nil)))
        (.primitive .after .nil (.ret (.cons (.output (2 : Fin 4) (.tail .head)) .nil)))))

private def joinLambdas (wrong : Bool) : ModuleTerm Op single seedSigs [[exportFn.port]] [exportFn.port] :=
  .bind (.lambda (joinBinding wrong).term) (.ret (lastExport seedSigs exportFn))

private def joinPlan (cap : Nat) (wrong : Bool) :
    Plan (one cap) (one cap) (Scope.seed inferred (one cap) (one cap))
      (joinBinding wrong).summary (joinLambdas wrong) :=
  Plan.finishDirect (scope := Scope.seed inferred (one cap) (one cap)) (joinBinding wrong)

private def joinAdmitted (cap : Nat) (wrong : Bool) :=
  (joinPlan cap wrong).admit inferred actions 83 (one cap) (one cap) 20 (relayReady cap) (relayReady cap)

private def joinExport (cap : Nat) := (joinAdmitted cap false).get (by rfl)

example (cap : Nat) : joinAdmitted cap true = none := rfl

private theorem joinSpareDead : Address.arg 5 ∉ (joinBinding false).summary.live requested := by decide

private theorem joinAgreed (cap count : Nat) :
    Ordered.InputsAgree (m := machine) (joinBinding false).summary requested
      (prependContext (args count 41 4) (joinExport cap).capsL)
      (prependContext (args count 41 40) (joinExport cap).capsR) := by
  intro ty p live
  let scope := Scope.seed inferred (one cap) (one cap)
  let captured := (joinBinding false).captures.read (one cap) scope.localsL
  change (prependContext (args count 41 4) captured).get p = (prependContext (args count 41 40) captured).get p
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · rfl
  cases p with
  | head => exact False.elim (joinSpareDead live)
  | tail p => nomatch p

private def runJoin (wrong : Bool) (fuel cap count spare : Nat) :=
  Executable.run actions fuel 83 (seededGraph inferred (joinLambdas wrong)) (one cap) .head (args count 41 spare) 20

example (fuel after cap count : Nat) :
    ∃ left right, runJoin false fuel cap count 4 = .ok left ∧ runJoin false fuel cap count 40 = .ok right ∧
      PrefixObservationsAgree actions requested after left right :=
  Ordered.Prefix.Export.linked_prefixes_agree (actions := actions) (summary := (joinBinding false).summary)
    requested fuel after 83 (seededGraph inferred (joinLambdas false)) (one cap) (one cap)
    (args count 41 4) (args count 41 40) 20 (joinExport cap) (joinAgreed cap count)

private def joinBlock (cap count spare : Nat) : Option (Nat × Nat) :=
  match runJoin false 80 cap count spare with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, .cons (.data operand) .nil⟩, _⟩ store) => some (operand, store)
  | _ => none

#guard (runJoin false 80 2 1 4).toOption.bind wrapperResult == some (41, 44)
#guard (runJoin false 80 2 1 40).toOption.bind wrapperResult == some (41, 44)
#guard joinBlock 2 0 4 == some (0, 21)
#guard joinBlock 2 0 40 == some (0, 21)
#guard (resume (runJoin false 80 2 0 4)).bind wrapperResult == some (41, 63)
#guard (resume (runJoin false 80 2 0 40)).bind wrapperResult == some (41, 63)
#guard joinBlock 0 1 4 == some (0, 32)
#guard (resume (runJoin false 80 0 1 4)).bind wrapperResult == some (41, 60)
#guard (resume (runJoin true 80 2 0 4)).bind wrapperResult == some (41, 63)
#guard (runJoin true 80 2 1 4).toOption.bind wrapperResult == some (0, 45)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Regression
