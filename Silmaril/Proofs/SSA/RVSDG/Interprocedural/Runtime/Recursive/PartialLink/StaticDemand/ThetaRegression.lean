module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.ThetaRegression

open NestedTheta.Liveness
open Continuation.Partial.Executable (Actions Observation observe runFor)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev single := [num]
private abbrev pair := [num, num]
private abbrev decision : List T := [.control 2]
private abbrev callee : Function Unit Unit := ⟨single, single⟩
private abbrev caller : Function Unit Unit := ⟨[num, num, num, num], pair⟩
private abbrev callerContext := [callee.port, num]
private abbrev carried := callerContext ++ caller.args

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | probe : Op pair single
  | choose : Op single decision
  | suffix : Op single single

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .probe, .cons (.data captured) (.cons (.data request) .nil) =>
      .cons (.data (captured + request)) .nil
    | .choose, _ => .cons (.control 0) .nil
    | .suffix, input => input

private def one (a : Nat) : Tuple machine.Val single := .cons (.data a) .nil
private def two (a b : Nat) : Tuple machine.Val pair := .cons (.data a) (.cons (.data b) .nil)

private def actions : Actions machine Nat where
  step
    | .probe, .cons (.data captured) (.cons (.data request) .nil) => fun store =>
      let captured : Nat := captured
      let request : Nat := request
      if captured = 7 ∧ request = 0 then none
      else some (one (captured + request + store), store + 2)
    | .choose, .cons (.data request) .nil => fun store =>
      let request : Nat := request
      let tag : Fin 2 := if request = 1 ∨ (request = 0 ∧ 50 ≤ store) then 1 else 0
      some (.cons (.control tag) .nil, store)
    | .suffix, .cons (.data value) .nil => fun store =>
      let value : Nat := value
      some (one (value + store), store + 5)

private def calleeCode : Code Op (single ++ callee.args) [] [single] callee.results true :=
  .primitive .probe (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def capture : Port carried num := .tail .head
private def request : Port carried num := .tail (.tail .head)
private def seed : Port carried num := .tail (.tail (.tail .head))
private def payload : Port carried num := .tail (.tail (.tail (.tail .head)))
private def dead : Port carried num := .tail (.tail (.tail (.tail (.tail .head))))

/-- Feedback supplies the seed as the next request. The closure, its capture
witness, the seed, and the dead port are forwarded unchanged. -/
private def body : Code Op carried [] [single, decision] (Theta.BodyResults carried) true :=
  let feedback : Wires carried [single, decision] (Theta.BodyResults carried) :=
    .cons (.output (1 : Fin 2) .head)
      (.cons (.arg .head) (.cons (.arg capture) (.cons (.arg seed) (.cons (.arg seed)
        (.cons (.output (0 : Fin 2) .head) (.cons (.arg dead) .nil))))))
  .apply (fn := callee) .head (.cons (.arg capture) .nil) calleeCode (.cons (.arg request) .nil)
    (.primitive .choose (.cons (.arg request) .nil) (.ret feedback))

private def callerCode : Code Op carried [] [carried, single] caller.results true :=
  let carriedWires : Wires carried [] carried :=
    .cons (.arg .head) (.cons (.arg capture) (.cons (.arg request) (.cons (.arg seed)
      (.cons (.arg payload) (.cons (.arg dead) .nil)))))
  .theta carriedWires body
    (.primitive .suffix (.cons (.output (0 : Fin 1) payload) .nil)
      (.ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) dead) .nil))))

private def graph : Omega Op single [caller.port] [[callee.port], [caller.port]] :=
  OmegaTerm.toGraph ⟨.bind (.lambda ⟨single, .cons (.arg .head) .nil, [single], calleeCode.term⟩)
    (.bind (.lambda ⟨callerContext, .cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil),
      [carried, single], callerCode.term⟩)
      (.ret (.cons (.output (1 : Fin 2) .head) .nil)))⟩

private def requested : Demand := fun p => p == 0
private def loopExit : Demand := fun p => p == 4
private def firstRound : Feedback.Mask carried.length :=
  Feedback.step loopExit (fun d => (body.plan d).live) ∅

-- The seed is discovered only when demand is fed back through the request.
example : Feedback.includes firstRound 3 = false := by decide
example : Feedback.includes (body.feedbackLive loopExit) 3 = true := by decide
example : Feedback.includes (body.feedbackLive loopExit) 5 = false := by decide
example : callerCode.liveIn requested = [.arg 1, .arg 2, .arg 3] := by decide

private def params (req next dead : Nat) : Tuple machine.Val caller.args :=
  .cons (.data req) (.cons (.data next) (two 99 dead))

private def captures (cap : Nat) : Tuple machine.Val callerContext :=
  .cons (.closure (one cap) calleeCode.term.toGraph) (one cap)

private def exports (cap : Nat) : Tuple machine.Val [caller.port] :=
  .cons (.closure (captures cap) callerCode.term.toGraph) .nil

private theorem resolved (cap req next dead : Nat) :
    callerCode.Resolved (prependContext (params req next dead) (captures cap)) := by
  intro locals
  cases locals
  constructor
  · intro now stable
    have target : now.get .head = .closure (one cap) calleeCode.term.toGraph := stable .head rfl
    have capValue : now.get capture = .data cap := stable capture rfl
    refine ⟨?_, fun _ _ => trivial, fun _ _ => trivial⟩
    change now.get .head = .closure (.cons (now.get capture) .nil) calleeCode.term.toGraph
    rw [target, capValue]
    rfl
  · exact fun _ _ => trivial

private theorem agree (cap req next deadL deadR : Nat) :
    callerCode.AgreesOnInputs requested
      (prependContext (params req next deadL) (captures cap))
      (prependContext (params req next deadR) (captures cap)) := by
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
        | head => rfl
        | tail p =>
          cases p with
          | head => rfl
          | tail p =>
            cases p with
            | head => exact False.elim ((by decide : Address.arg 5 ∉ callerCode.liveIn requested) live)
            | tail p => nomatch p

private def run (fuel req next dead : Nat) :=
  Executable.run actions fuel 82 graph (one 7) .head (params req next dead) 20

private theorem linked_pair (fuel after req next : Nat) :
    ∃ left right, run fuel req next 4 = .ok left ∧ run fuel req next 40 = .ok right ∧
      PrefixObservationsAgree actions requested after left right :=
  callerCode.linked_prefixes_agree (fn := caller) (context := callerContext) actions requested fuel after
    graph 82 .head (one 7) (one 7) (params req next 4) (params req next 40) 20
    (exportsL := exports 7) (exportsR := exports 7) (middle := 20)
    (capsL := captures 7) (capsR := captures 7) rfl rfl rfl rfl
    (resolved 7 req next 4) (resolved 7 req next 40) (agree 7 req next 4 40)

private def probeBlock (atStore : Nat) (outcome : Observation machine Nat pair) : Prop :=
  match outcome with
  | .blocked ⟨⟨_, _, .probe, _, _, operands⟩, frames⟩ store =>
    operands = two 7 0 ∧ store = atStore ∧ Continuation.Descent.stackDepth frames = 4
  | _ => False

private def checksBlock (atStore : Nat) (result : Except (Failure machine Nat) (Observation machine Nat pair)) : Prop :=
  match result with
  | .ok outcome => probeBlock atStore outcome
  | .error _ => False

-- The first probe updates the store. The next request comes from feedback.
example : checksBlock 22 (run 50 1 0 4) := ⟨rfl, rfl, rfl⟩
example : checksBlock 22 (run 50 1 0 40) := ⟨rfl, rfl, rfl⟩

-- A different seed permits a second effect and returns through the suffix.
example : run 50 1 3 4 = .ok (.returned (two 56 4) 29) := rfl
example : run 50 1 3 40 = .ok (.returned (two 56 40) 29) := rfl

private def resumeProbe (middle : Nat) (result : Except (Failure machine Nat) (Observation machine Nat pair)) :
    Option (Observation machine Nat pair) :=
  match result with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, _⟩, frames⟩ _) =>
    some (observe actions (runFor actions 50 ⟨.returned (one 10) frames, middle⟩))
  | _ => none

-- At store 40 resumption exits θ and runs the effectful caller suffix.
example : resumeProbe 40 (run 50 1 0 4) = some (.returned (two 50 4) 45) := rfl
example : resumeProbe 40 (run 50 1 0 40) = some (.returned (two 50 40) 45) := rfl

private def checksRestart (result : Option (Observation machine Nat pair)) : Prop :=
  match result with
  | some outcome => probeBlock 50 outcome
  | none => False

-- At store 50 the same resumption instead restarts and hits the probe again.
example : checksRestart (resumeProbe 50 (run 50 1 0 4)) := ⟨rfl, rfl, rfl⟩
example : checksRestart (resumeProbe 50 (run 50 1 0 40)) := ⟨rfl, rfl, rfl⟩

-- Feeding request 1 back retains a live configuration at this budget.
example : ∃ config, run 80 1 1 4 = .ok (.suspended config) := ⟨_, rfl⟩
example : ∃ config, run 80 1 1 40 = .ok (.suspended config) := ⟨_, rfl⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.ThetaRegression
