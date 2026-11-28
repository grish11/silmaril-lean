module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Regression

open NestedTheta.Liveness (Demand)
open Continuation.Partial.Executable (Actions Observation observe runFor)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev single := [num]
private abbrev pair := [num, num]
private abbrev triple := [num, num, num]
private abbrev callee : Function Unit Unit := ⟨pair, pair⟩
private abbrev caller : Function Unit Unit := ⟨triple, triple⟩
private abbrev callerContext := [callee.port, num]
private abbrev callerEntry := callerContext ++ caller.args

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | probe : Op pair single
  | copy : Op single single

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .probe, .cons (.data captured) (.cons (.data request) .nil) =>
      .cons (.data (captured + request)) .nil
    | .copy, input => input

private def one (a : Nat) : Tuple machine.Val single := .cons (.data a) .nil

private def two (a b : Nat) : Tuple machine.Val pair := .cons (.data a) (.cons (.data b) .nil)

private def nums (a b c : Nat) : Tuple machine.Val triple :=
  .cons (.data a) (.cons (.data b) (.cons (.data c) .nil))

private def actions : Actions machine Nat where
  step
    | .probe, .cons (.data captured) (.cons (.data request) .nil) => fun store =>
      let captured : Nat := captured
      let request : Nat := request
      if captured = 7 ∧ request = 0 then none
      else some (one (if request = 1 then 0 else captured + request + store), store + 2)
    | .copy, input => fun store => some (input, store)

/-- The callee observes the capture and request at the probe.
Its second output forwards the other formal argument. -/
private def calleeCode : Code Op (single ++ callee.args) [] [single, single] callee.results :=
  .primitive .probe (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.primitive .copy (.cons (.output (0 : Fin 1) .head) .nil)
      (.ret (.cons (.output (1 : Fin 2) .head) (.cons (.arg (.tail (.tail .head))) .nil))))

/-- The first call's computed result feeds the second call's primitive.
The requested final results select port 0 of the first call and port 1
of the second. The first call's forwarded argument is dead. -/
private def callerCode : Code Op callerEntry [] [pair, pair] caller.results :=
  let captures : Wires callerEntry [] single := .cons (.arg (.tail .head)) .nil
  let request : Port callerEntry num := .tail (.tail .head)
  let forwarded : Port callerEntry num := .tail (.tail (.tail .head))
  let dead : Port callerEntry num := .tail (.tail (.tail (.tail .head)))
  let results : Wires callerEntry [pair, pair] triple :=
    .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) (.cons (.arg dead) .nil))
  .apply (fn := callee) .head captures calleeCode
    (.cons (.arg request) (.cons (.arg dead) .nil))
    (.apply (fn := callee) .head captures calleeCode
      (.cons (.output (0 : Fin 1) .head) (.cons (.arg forwarded) .nil)) (.ret results))

private def graph : Omega Op single [caller.port] [[callee.port], [caller.port]] :=
  OmegaTerm.toGraph ⟨.bind (.lambda ⟨single, .cons (.arg .head) .nil, [single, single], calleeCode.term⟩)
    (.bind (.lambda ⟨callerContext, .cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil),
      [pair, pair], callerCode.term⟩)
      (.ret (.cons (.output (1 : Fin 2) .head) .nil)))⟩

private def requested : Demand := fun p => p < 2

example : calleeCode.liveIn (fun p => p == 0) = [.arg 0, .arg 1] := by decide
example : calleeCode.liveIn (fun p => p == 1) = [.arg 0, .arg 1, .arg 2] := by decide
example : (callerCode.plan requested).reads =
    [[.arg 1, .arg 2], [.arg 1, .output 0 0, .arg 3], [.output 0 0, .output 1 1]] := by decide
example : callerCode.liveIn requested = [.arg 1, .arg 2, .arg 3] := by decide
example : callerCode.liveIn (fun _ => false) = [.arg 1, .arg 2] := by decide
example : Address.arg 1 ∈ (callerCode.liveness requested).mayOut 0 :=
  (callerCode.mem_liveIn_iff requested _).1 (by decide)

private def captures (cap : Nat) : Tuple machine.Val callerContext :=
  .cons (.closure (one cap) calleeCode.term.toGraph) (one cap)

private def exports (cap : Nat) : Tuple machine.Val [caller.port] :=
  .cons (.closure (captures cap) callerCode.term.toGraph) .nil

private theorem resolved (cap first pass dead : Nat) :
    callerCode.Resolved (prependContext (nums first pass dead) (captures cap)) :=
  fun _ => ⟨rfl, fun _ _ _ => trivial, fun _ => ⟨rfl, fun _ _ _ => trivial, fun _ => trivial⟩⟩

private theorem agree (cap first pass deadL deadR : Nat) :
    callerCode.AgreesOnInputs requested
      (prependContext (nums first pass deadL) (captures cap))
      (prependContext (nums first pass deadR) (captures cap)) := by
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
          | head => exact False.elim ((by decide : Address.arg 4 ∉ callerCode.liveIn requested) live)
          | tail p => nomatch p

private def run (fuel cap first dead : Nat) :=
  Executable.run actions fuel 73 graph (one cap) .head (nums first 11 dead) 20

private theorem linked_pair (first : Nat) :
    ∃ fuel left right, run fuel 7 first 4 = .ok left ∧ run fuel 7 first 40 = .ok right ∧
      EndpointsAgree actions requested left right :=
  callerCode.linked_runs_agree (fn := caller) (context := callerContext) actions requested graph 73 .head
    (one 7) (one 7) (nums first 11 4) (nums first 11 40) 20
    (exportsL := exports 7) (exportsR := exports 7) (middle := 20)
    (capsL := captures 7) (capsR := captures 7) rfl rfl rfl rfl
    (resolved 7 first 11 4) (resolved 7 first 11 40) (agree 7 first 11 4 40)

-- Both call sites execute and update the store. Only the last result varies.
example : run 40 7 3 4 = .ok (.returned (nums 30 11 4) 24) := rfl
example : run 40 7 3 40 = .ok (.returned (nums 30 11 40) 24) := rfl

private def isProbeBlock (inputStore : Nat) (outcome : Observation machine Nat triple) : Prop :=
  match outcome with
  | .blocked ⟨⟨_, _, .probe, _, _, operands⟩, frames⟩ store =>
    operands = two 7 0 ∧ store = inputStore ∧ Continuation.Descent.stackDepth frames = 2
  | _ => False

private def Checks (p : Observation machine Nat triple → Prop)
    (result : Except (Failure machine Nat) (Observation machine Nat triple)) : Prop :=
  match result with
  | .ok outcome => p outcome
  | .error _ => False

-- The second apply still executes even though its computed data result is dead.
example : Checks (isProbeBlock 22) (run 40 7 1 4) := ⟨rfl, rfl, rfl⟩
example : Checks (isProbeBlock 22) (run 40 7 1 40) := ⟨rfl, rfl, rfl⟩

-- Changing the live capture unblocks the second invocation.
example : run 40 8 1 40 = .ok (.returned (nums 0 11 40) 24) := rfl

private def resumeFirst (outcome : Observation machine Nat triple) : Prop :=
  match outcome with
  | .blocked ⟨⟨_, _, .probe, _, _, _⟩, frames⟩ _ =>
    isProbeBlock 50 (observe actions (runFor actions 40 ⟨.returned (one 0) frames, 50⟩))
  | _ => False

-- Supplying a result to the first blocked probe reaches the next call and
-- blocks again at the supplied store. The saved suffix is real runtime work.
example : Checks (isProbeBlock 20) (run 40 7 0 4) := ⟨rfl, rfl, rfl⟩
example : Checks resumeFirst (run 40 7 0 4) := ⟨rfl, rfl, rfl⟩
example : Checks resumeFirst (run 40 7 0 40) := ⟨rfl, rfl, rfl⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Regression
