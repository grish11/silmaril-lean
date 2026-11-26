module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.GammaRegression

open NestedTheta.Liveness (Demand)
open Continuation.Partial.Executable (Actions Observation observe runFor)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev single := [num]
private abbrev pair := [num, num]
private abbrev callee : Function Unit Unit := ⟨single, single⟩
private abbrev caller : Function Unit Unit := ⟨[.control 2, num, num, num], pair⟩
private abbrev callerContext := [callee.port, num]
private abbrev callerEntry := callerContext ++ caller.args
private abbrev armEntry := [callee.port, num, num, num, num]

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | probe : Op pair single
  | suffix : Op single single

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .probe, .cons (.data captured) (.cons (.data request) .nil) =>
      .cons (.data (captured + request)) .nil
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
    | .suffix, .cons (.data input) .nil => fun store =>
      let input : Nat := input
      some (one (input + store), store + 5)

private def calleeCode : Code Op (single ++ callee.args) [] [single] callee.results :=
  .primitive .probe (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def armCall : Code Op armEntry [] [single] pair :=
  .apply (fn := callee) .head (.cons (.arg (.tail .head)) .nil) calleeCode
    (.cons (.arg (.tail (.tail .head))) .nil)
    (.ret (.cons (.output (0 : Fin 1) .head)
      (.cons (.arg (.tail (.tail (.tail (.tail .head))))) .nil)))

private def armFallback : Code Op armEntry [] [] pair :=
  .ret (.cons (.arg (.tail (.tail (.tail .head))))
    (.cons (.arg (.tail (.tail (.tail (.tail .head))))) .nil))

private def armSigs : Fin 2 → List (Ports T) := Fin.cases [single] (fun _ => [])

private def arms (i : Fin 2) : Code Op armEntry [] (armSigs i) pair :=
  Fin.cases (motive := fun j => Code Op armEntry [] (armSigs j) pair) armCall (fun _ => armFallback) i

/-- After γ the effectful suffix reads its first exit. The second exit is
forwarded only to the undemanded result. -/
private def callerCode : Code Op callerEntry [] [pair, single] caller.results :=
  let wires : Wires callerEntry [] armEntry :=
    .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail (.tail .head))))
      (.cons (.arg (.tail (.tail (.tail (.tail .head)))))
        (.cons (.arg (.tail (.tail (.tail (.tail (.tail .head)))))) .nil))))
  .gamma 0 armSigs (.arg (.tail (.tail .head))) wires arms
    (.primitive .suffix (.cons (.output (0 : Fin 1) .head) .nil)
      (.ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) (.tail .head)) .nil))))

private def graph : Omega Op single [caller.port] [[callee.port], [caller.port]] :=
  OmegaTerm.toGraph ⟨.bind (.lambda ⟨single, .cons (.arg .head) .nil, [single], calleeCode.term⟩)
    (.bind (.lambda ⟨callerContext, .cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil),
      [pair, single], callerCode.term⟩)
      (.ret (.cons (.output (1 : Fin 2) .head) .nil)))⟩

private def requested : Demand := fun p => p == 0

example : armCall.liveIn requested = [.arg 1, .arg 2] := by decide
example : armFallback.liveIn requested = [.arg 3] := by decide
example : (callerCode.plan requested).reads =
    [[.arg 2, .arg 1, .arg 3, .arg 4], [.output 0 0], [.output 1 0]] := by decide
example : callerCode.liveIn requested = [.arg 2, .arg 1, .arg 3, .arg 4] := by decide
example : Address.arg 2 ∈ (callerCode.liveness requested).mayOut 0 :=
  (callerCode.mem_liveIn_iff requested _).1 (by decide)
example : Address.arg 5 ∉ (callerCode.liveness requested).mayOut 0 := fun live =>
  (by decide : Address.arg 5 ∉ callerCode.liveIn requested) ((callerCode.mem_liveIn_iff requested _).2 live)

private def params (tag : Fin 2) (request fallback dead : Nat) : Tuple machine.Val caller.args :=
  .cons (.control tag) (.cons (.data request) (two fallback dead))

private def captures (cap : Nat) : Tuple machine.Val callerContext :=
  .cons (.closure (one cap) calleeCode.term.toGraph) (one cap)

private def exports (cap : Nat) : Tuple machine.Val [caller.port] :=
  .cons (.closure (captures cap) callerCode.term.toGraph) .nil

private theorem resolved (cap : Nat) (tag : Fin 2) (request dead : Nat) :
    callerCode.Resolved (prependContext (params tag request 9 dead) (captures cap)) := by
  intro locals
  cases locals
  constructor
  · intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact ⟨rfl, fun _ _ => trivial, fun _ => trivial⟩
    · trivial
  · exact fun _ _ _ _ => trivial

private theorem agree (cap : Nat) (tag : Fin 2) (request deadL deadR : Nat) :
    callerCode.AgreesOnInputs requested
      (prependContext (params tag request 9 deadL) (captures cap))
      (prependContext (params tag request 9 deadR) (captures cap)) := by
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

private def run (fuel : Nat) (tag : Fin 2) (request dead : Nat) :=
  Executable.run actions fuel 81 graph (one 7) .head (params tag request 9 dead) 20

private theorem linked_pair (tag : Fin 2) (request : Nat) :
    ∃ fuel left right, run fuel tag request 4 = .ok left ∧ run fuel tag request 40 = .ok right ∧
      EndpointsAgree actions requested left right :=
  callerCode.linked_runs_agree (fn := caller) (context := callerContext) actions requested graph 81 .head
    (one 7) (one 7) (params tag request 9 4) (params tag request 9 40) 20
    (exportsL := exports 7) (exportsR := exports 7) (middle := 20)
    (capsL := captures 7) (capsR := captures 7) rfl rfl rfl rfl
    (resolved 7 tag request 4) (resolved 7 tag request 40) (agree 7 tag request 4 40)

-- The call is followed by the effectful γ suffix. The fallback skips the probe.
example : run 32 0 3 4 = .ok (.returned (two 52 4) 27) := rfl
example : run 32 0 3 40 = .ok (.returned (two 52 40) 27) := rfl
example : run 32 1 0 4 = .ok (.returned (two 29 4) 25) := rfl

private def probeBlock (result : Except (Failure machine Nat) (Observation machine Nat pair)) : Prop :=
  match result with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, operands⟩, frames⟩ store) =>
    operands = two 7 0 ∧ store = 20 ∧ Continuation.Descent.stackDepth frames = 3
  | _ => False

example : probeBlock (run 32 0 0 4) := ⟨rfl, rfl, rfl⟩
example : probeBlock (run 32 0 0 40) := ⟨rfl, rfl, rfl⟩

private def resumeProbe (result : Except (Failure machine Nat) (Observation machine Nat pair)) :
    Option (Observation machine Nat pair) :=
  match result with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, _⟩, frames⟩ _) =>
    some (observe actions (runFor actions 32 ⟨.returned (one 10) frames, 50⟩))
  | _ => none

-- Resumption supplies the call's result and then executes the actual γ suffix.
example : resumeProbe (run 32 0 0 4) = some (.returned (two 60 4) 55) := rfl
example : resumeProbe (run 32 0 0 40) = some (.returned (two 60 40) 55) := rfl

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.GammaRegression
