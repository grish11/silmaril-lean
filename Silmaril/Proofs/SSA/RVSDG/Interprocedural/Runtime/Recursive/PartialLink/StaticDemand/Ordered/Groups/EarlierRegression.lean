module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Synthesis.Defs
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Synthesis.Defs
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.EarlierRegression

open NestedTheta.Liveness
open Continuation.Partial.Executable (Actions Observation observe runFor)
open Ordered.Prefix (Plan Scope lastExport)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev single := [num]
private abbrev decision : List T := [.control 2, num]
private abbrev earlyFn : Function Unit Unit := ⟨single, single⟩
private abbrev lateFn : Function Unit Unit := ⟨[num, num, num], single⟩

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | decrement : Op single decision
  | probe : Op single []
  | finish : Op [] []

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .decrement, .cons (.data n) .nil => .cons (.control 0) (.cons (.data n) .nil)
    | .probe, _ => .nil
    | .finish, _ => .nil

private def one (n : Nat) : Tuple machine.Val single := .cons (.data n) .nil

private def actions : Actions machine Nat where
  step
    | .decrement, .cons (.data n) .nil => fun store =>
      let n : Nat := n
      let flag : Fin 2 := if n = 0 then 0 else 1
      some (.cons (.control flag) (one (n - 1)), store + 1)
    | .probe, .cons (.data n) .nil => fun store =>
      let n : Nat := n
      if n = 0 then none else some (.nil, store + n)
    | .finish, _ => fun store => some (.nil, store + 10)

private abbrev start := Scope.ordinary machine

private def prelude : Binding Op start.table single [] earlyFn where
  context := []
  captures := .nil
  sigs := [[]]
  body := .primitive .finish .nil (.ret (.cons (.arg .head) .nil))

private def beforeFirst (cap : Nat) := start.add prelude (one cap) (one cap)
private abbrev firstTable := (beforeFirst 0).table

private abbrev earlyShape : MemberSummaries Unit Unit :=
  .signaturesOnly [earlyFn] (fun _ => single)

private abbrev earlyPorts := memberPorts earlyShape.members

private def earlyBody :
    Code Op [earlyFn.port, num, num] [] [[]] single true (some (Ordered.append firstTable earlyShape)) :=
  .primitive .probe (.cons (.arg (.tail .head)) .nil)
    (.ret (.cons (.arg (.tail (.tail .head))) .nil))

private def earlyTemplate : (beforeFirst 0).GroupTemplate earlyShape single where
  context := single
  captures := .cons (.arg .head) .nil
  memberWires i := Fin.cases (.cons (.arg (.tail .head)) (.cons (.arg .head) .nil)) (fun j => j.elim0) i
  sigs := fun _ => [[]]
  body i := Fin.cases earlyBody (fun j => j.elim0) i

private theorem earlySafe : earlyTemplate.ReferenceSafe := by
  unfold Family.Template.ReferenceSafe
  decide

private def early := (beforeFirst 0).synthesizeGroup earlyTemplate earlySafe

private def beforeSecond (cap : Nat) := (beforeFirst cap).addGroup early (one cap) (one cap)
private abbrev secondTable := (beforeSecond 0).table

private theorem earlyReady (cap : Nat) :
    early.family.ReadyWith (early.read (one cap) (beforeFirst cap).localsL)
      ((beforeFirst cap).guardL.combine (early.family.guard (early.read (one cap) (beforeFirst cap).localsL))) := by
  intro i
  obtain rfl := Fin.eq_zero i
  exact ⟨rfl, fun _ _ _ => trivial⟩

private abbrev laterShape : MemberSummaries Unit Unit :=
  .signaturesOnly [lateFn] (fun _ => [earlyFn.port, num])

private abbrev templateSlots := Ordered.append secondTable laterShape
private abbrev firstGroupSlot := rightIndex firstTable earlyTemplate.summaries (0 : Fin 1)
private abbrev earlySlot := leftIndex secondTable laterShape firstGroupSlot
private abbrev lateSlot := rightIndex secondTable laterShape (0 : Fin 1)
private abbrev latePorts := memberPorts laterShape.members

private abbrev lateEntry := [lateFn.port, earlyFn.port, num, num, num, num]
private def capturedTarget : Port lateEntry earlyFn.port := .tail .head
private def capture : Port lateEntry num := .tail (.tail .head)
private def counter : Port lateEntry num := .tail (.tail (.tail .head))
private def payload : Port lateEntry num := .tail (.tail (.tail (.tail .head)))
private def spare : Port lateEntry num := .tail (.tail (.tail (.tail (.tail .head))))

private def base : Code Op lateEntry [] [single] single true (some templateSlots) :=
  .familyCall (table := templateSlots) earlySlot capturedTarget (.cons (.arg capture) .nil)
    (.cons (.arg payload) .nil) (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def recurse : Code Op lateEntry [] [single, []] single true (some templateSlots) :=
  .familyCall (table := templateSlots) lateSlot .head (.cons (.arg capturedTarget) (.cons (.arg capture) .nil))
    (.cons (.arg counter) (.cons (.arg payload) (.cons (.arg spare) .nil)))
    (.primitive .finish .nil (.ret (.cons (.output (0 : Fin 2) .head) .nil)))

private def armSigs (i : Fin 2) : List (Ports T) := Fin.cases [single] (fun _ => [single, []]) i

private def arms (i : Fin 2) : Code Op lateEntry [] (armSigs i) single true (some templateSlots) :=
  Fin.cases (motive := fun j => Code Op lateEntry [] (armSigs j) single true (some templateSlots))
    base (fun _ => recurse) i

private def lateBody : Code Op lateEntry [] [decision, single] single true (some templateSlots) :=
  let wires : Wires lateEntry [decision] lateEntry :=
    .cons (.arg .head) (.cons (.arg capturedTarget) (.cons (.arg capture)
      (.cons (.output (0 : Fin 1) (.tail .head)) (.cons (.arg payload) (.cons (.arg spare) .nil)))))
  .primitive .decrement (.cons (.arg counter) .nil)
    (.gamma 0 armSigs (.output (0 : Fin 1) .head) wires arms
      (.ret (.cons (.output (1 : Fin 2) .head) .nil)))

private def template : (beforeSecond 0).GroupTemplate laterShape single where
  context := [earlyFn.port, num]
  captures := .cons (.output (1 : Fin 2) .head) (.cons (.arg .head) .nil)
  memberWires i := Fin.cases
    (.cons (.arg (.tail (.tail .head))) (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil)))
    (fun j => j.elim0) i
  sigs := fun _ => [decision, single]
  body i := Fin.cases lateBody (fun j => j.elim0) i

private theorem safe : template.ReferenceSafe := by
  unfold Family.Template.ReferenceSafe
  decide

private def group := (beforeSecond 0).synthesizeGroup template safe
private abbrev late := group.family

private def finalScope (cap : Nat) := (beforeSecond cap).addGroup group (one cap) (one cap)
private abbrev slots := (finalScope 0).table

set_option maxHeartbeats 2400000 in
private theorem lateReady (cap : Nat) :
    late.ReadyWith (group.read (one cap) (beforeSecond cap).localsL) ((beforeSecond cap).guardL.combine
      (late.guard (group.read (one cap) (beforeSecond cap).localsL))) := by
  intro i
  obtain rfl := Fin.eq_zero i
  refine ⟨rfl, ?_⟩
  intro args locals outputs
  refine ⟨?_, fun _ _ _ => trivial⟩
  intro arm
  refine Fin.cases ?_ (fun _ => ?_) arm
  · exact ⟨⟨rfl, rfl⟩, fun _ => trivial⟩
  · exact ⟨⟨rfl, rfl⟩, fun _ _ => trivial⟩

private abbrev past := [[earlyFn.port], earlyPorts, latePorts]
private abbrev wrapperContext := [lateFn.port, earlyFn.port, num, earlyFn.port]
private abbrev wrapperEntry := wrapperContext ++ lateFn.args
private abbrev preludeSlot := leftIndex secondTable template.summaries
  (leftIndex firstTable earlyTemplate.summaries (0 : Fin 1))
private abbrev lateExportSlot := rightIndex secondTable template.summaries (0 : Fin 1)

private def wrapperBody : Code Op wrapperEntry [] [single, single] single true (some slots) :=
  .familyCall (table := slots) lateExportSlot .head (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))
    (.cons (.arg (.tail (.tail (.tail (.tail .head)))))
      (.cons (.arg (.tail (.tail (.tail (.tail (.tail .head))))))
        (.cons (.arg (.tail (.tail (.tail (.tail (.tail (.tail .head))))))) .nil)))
    (.callAt (table := slots) preludeSlot (.arg (.tail (.tail (.tail .head)))) .nil
      (.cons (.output (0 : Fin 1) .head) .nil)
      (.ret (.cons (.output (1 : Fin 2) .head) .nil)))

private def wrapper : Binding Op slots single past lateFn where
  context := wrapperContext
  captures := .cons (.output (2 : Fin 3) .head)
    (.cons (.output (1 : Fin 3) .head) (.cons (.arg .head) (.cons (.output (0 : Fin 3) .head) .nil)))
  sigs := [single, single]
  body := wrapperBody

private def source : OmegaTerm Op single [lateFn.port] ([[earlyFn.port], earlyPorts, latePorts, [lateFn.port]]) :=
  ⟨.bind (.lambda prelude.term) (.bind (.phi early.term) (.bind (.phi group.term)
    (.bind (.lambda wrapper.term) (.ret (lastExport past lateFn)))))⟩

private def numbered := source.toGraph

set_option maxHeartbeats 1400000 in
private theorem wrapperReady (cap : Nat) :
    wrapper.resolved (finalScope cap).guardL (one cap) (finalScope cap).localsL :=
  fun _ _ => ⟨⟨rfl, rfl⟩, fun _ => ⟨⟨rfl, rfl⟩, fun _ => trivial⟩⟩

private def plan (cap : Nat) :
    Plan (one cap) (one cap) start wrapper.summary source.region :=
  .lambda (scope := start) prelude (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    (.phiWithEarlier (scope := beforeFirst cap) early (earlyReady cap) (earlyReady cap)
      (.phiWithEarlier (scope := beforeSecond cap) group (lateReady cap) (lateReady cap)
        (.finish (scope := finalScope cap) wrapper (wrapperReady cap) (wrapperReady cap))))

private def admitted (cap : Nat) :=
  (plan cap).analyzeNumberedFromOrdinary actions 83 numbered (one cap) (one cap) 20 (OmegaTerm.toTerm_toGraph source)

private def analysis (cap : Nat) := (admitted cap).get (by rfl)
private def requested : Demand := (· == 0)
private def noResults : Demand := fun _ => false

#guard earlyTemplate.summaries.live (0 : Fin 1) noResults == [.arg 0]
#guard earlyTemplate.summaries.live (0 : Fin 1) requested == [.arg 0, .arg 1]
#guard template.summaries.live (0 : Fin 1) noResults == [.arg 1, .arg 2]
#guard template.summaries.live (0 : Fin 1) requested == [.arg 1, .arg 2, .arg 3]

#guard (analysis 3).liveCapture noResults (.tail (.tail .head))
#guard (analysis 3).liveFormal noResults .head
#guard (analysis 3).liveFormal requested (.tail .head)
#guard !(analysis 3).liveFormal noResults (.tail .head)
#guard !(analysis 3).liveFormal requested (.tail (.tail .head))

example : Address.arg 5 ∈ ((analysis 3).problem requested).mayOut 0 :=
  ((analysis 3).mem_liveIn_iff requested _).1 (by decide)

example : Address.arg 5 ∉ ((analysis 3).problem noResults).mayOut 0 :=
  fun h => (by decide : Address.arg 5 ∉ (analysis 3).liveIn noResults)
    (((analysis 3).mem_liveIn_iff noResults _).2 h)

private def args (spare : Nat) : Tuple machine.Val lateFn.args :=
  .cons (.data (1 : Nat)) (.cons (.data (41 : Nat)) (one spare))

private def run (fuel cap spare : Nat) :=
  Executable.run actions fuel 83 numbered (one cap) .head (args spare) 20

private def demand (want : Bool) : Demand := if want then requested else noResults

example (want : Bool) (fuel after cap : Nat) :
    ∃ left right, run fuel cap 4 = .ok left ∧ run fuel cap 40 = .ok right ∧
      PrefixObservationsAgree actions (demand want) after left right := by
  obtain ⟨left, right, ranL, ranR, agree⟩ :=
    (analysis cap).linked_substituteDeadFormals (demand want) fuel after (args 4) (args 40) (fun _ _ => rfl)
  have substituted : (analysis cap).substituteDeadFormals (demand want) (args 4) (args 40) = args 40 := by
    cases want <;> rfl
  rw [substituted] at ranR
  exact ⟨left, right, ranL, ranR, agree⟩

private def returned : Observation machine Nat single → Option (Nat × Nat)
  | .returned (.cons (.data payload) .nil) store => some (payload, store)
  | _ => none

private def blocked (spare : Nat) : Option (Nat × Nat) :=
  match run 80 0 spare with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, .cons (.data n) .nil⟩, _⟩ store) => some (n, store)
  | _ => none

private def resumed (spare : Nat) : Option (Nat × Nat) :=
  match run 80 0 spare with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, _⟩, stack⟩ _) =>
    returned (observe actions (runFor actions 80 ⟨.returned .nil stack, 50⟩))
  | _ => none

#guard (run 80 3 4).toOption.bind returned == some (41, 45)
#guard (run 80 3 40).toOption.bind returned == some (41, 45)
#guard blocked 4 == some (0, 22)
#guard blocked 40 == some (0, 22)
#guard resumed 4 == some (41, 70)
#guard resumed 40 == some (41, 70)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.EarlierRegression
