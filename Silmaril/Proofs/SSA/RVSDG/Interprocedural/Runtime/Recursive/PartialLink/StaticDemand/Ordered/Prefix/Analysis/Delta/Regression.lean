module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Remainder.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Synthesis.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Remainder.Thms
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Synthesis.Defs

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.DeltaRegression

open NestedTheta.Liveness (Demand)
open Continuation.Partial.Executable (Actions Observation observe runFor)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev global : T := .value (.global (.data ()))
private abbrev single := [num]
private abbrev pair := [num, num]
private abbrev member : Function Unit Unit := ⟨single, single⟩
private abbrev exportFn : Function Unit Unit := ⟨pair, single⟩

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | initialize (chargeInput : Bool) : Op single single
  | derive : Op [global] single
  | probe : Op [global] []
  | finish : Op [] []

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .initialize _, .cons (.data n) .nil => .cons (.data (2 * n)) .nil
    | .derive, .cons (.global _ _ (.data n)) .nil => .cons (.data (n + 1)) .nil
    | .probe, _ => .nil
    | .finish, _ => .nil

private def one (n : Nat) : Tuple machine.Val single := .cons (.data n) .nil

private def actions : Actions machine Nat where
  step
    | .initialize chargeInput, .cons (.data n) .nil => fun store =>
      let n : Nat := n
      some (one (2 * n), store + (if chargeInput then n else 0) + 4)
    | .derive, .cons (.global _ _ (.data n)) .nil => fun store =>
      let n : Nat := n
      some (one (n + 1), store + n + 5)
    | .probe, .cons (.global _ _ (.data n)) .nil => fun store =>
      let n : Nat := n
      if n = 0 then none else some (.nil, store + n)
    | .finish, _ => fun store => some (.nil, store + 10)

private def initializer (chargeInput : Bool) : RVSDG.Term Op single [] [single] single :=
  .bind ⟨single, .simple (.initialize chargeInput), .cons (.arg .head) .nil, fun i => i.elim0⟩
    (fun i => i.elim0) (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def delta : DeltaTerm Op single [] (.data ()) :=
  ⟨single, .cons (.arg .head) .nil, [single], initializer true⟩

private def initialized (cap : Nat) : Tuple machine.Val [global] :=
  .cons (.global 83 0 (.data (2 * cap))) .nil

private def receipt (cap : Nat) : DeltaPrefix actions 83 delta (one cap) (one cap) 20 :=
  ⟨initialized cap, initialized cap, 20 + cap + 4, rfl, rfl⟩

#guard ((DeltaPrefix.check actions 83 delta (one 3) (one 3) 20).map (·.store)) == some 27
#guard (DeltaPrefix.check actions 83 delta (one 3) (one 4) 20).isNone

private abbrev firstTable := (receipt 0).scope.table
private abbrev shape : MemberSummaries Unit Unit := .signaturesOnly [member] (fun _ => [global])

private def memberBody :
    Code Op [member.port, global, num] [] [[]] single true (some (Ordered.append firstTable shape)) :=
  .primitive .probe (.cons (.arg (.tail .head)) .nil)
    (.ret (.cons (.arg (.tail (.tail .head))) .nil))

private def template : (receipt 0).scope.GroupTemplate shape single where
  context := [global]
  captures := .cons (.output (0 : Fin 1) .head) .nil
  memberWires i := Fin.cases (.cons (.arg (.tail .head)) (.cons (.arg .head) .nil)) (fun j => j.elim0) i
  sigs := fun _ => [[]]
  body i := Fin.cases memberBody (fun j => j.elim0) i

private theorem safe : template.ReferenceSafe := by
  unfold Family.Template.ReferenceSafe
  decide

private def group := (receipt 0).scope.synthesizeGroup template safe

private theorem ready (cap : Nat) :
    group.family.ReadyWith (group.read (one cap) (receipt cap).scope.localsL) ((receipt cap).scope.guardL.combine
      (group.family.guard (group.read (one cap) (receipt cap).scope.localsL))) := by
  intro i
  obtain rfl := Fin.eq_zero i
  exact ⟨rfl, fun _ _ _ => trivial⟩

-- A stale global with the same payload cannot witness the capture.
example : ¬ group.family.guard (group.read (one 3) (receipt 3).scope.localsL) (0 : Fin 1)
    (group.family.memberValue (group.read (one 3) (receipt 3).scope.localsL) (0 : Fin 1))
    (.cons (.global 83 1 (.data (6 : Nat))) .nil) := by
  intro resolved
  have wrong : (Tuple.cons (.global 83 1 (.data (6 : Nat))) .nil : Tuple machine.Val [global]) =
      initialized 3 := resolved.2
  cases wrong

private def afterGroup (cap : Nat) := (receipt cap).scope.addGroup group (one cap) (one cap)
private abbrev slots := (afterGroup 0).table
private abbrev past := [[global], [member.port]]
private abbrev memberSlot := rightIndex firstTable template.summaries (0 : Fin 1)

private def wrapper : Binding Op slots single past exportFn where
  context := [member.port, global]
  captures := .cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil)
  sigs := [single, []]
  body := .familyCall (table := slots) memberSlot .head
    (.cons (.arg (.tail .head)) .nil) (.cons (.arg (.tail (.tail .head))) .nil)
    (.primitive .finish .nil (.ret (.cons (.output (0 : Fin 2) .head) .nil)))

private def tail : ModuleTerm Op single [[global]] [[member.port], [exportFn.port]] [exportFn.port] :=
  .bind (.phi group.term) (.bind (.lambda wrapper.term) (.ret (lastExport past exportFn)))

private def source : OmegaTerm Op single [exportFn.port] [[global], [member.port], [exportFn.port]] :=
  ⟨.bind (.delta delta) tail⟩

private def numbered := source.toGraph

set_option maxHeartbeats 800000 in
private theorem wrapperReady (cap : Nat) :
    wrapper.resolved (afterGroup cap).guardL (one cap) (afterGroup cap).localsL :=
  fun _ _ => ⟨⟨rfl, rfl⟩, fun _ _ => trivial⟩

private def plan (cap : Nat) :
    Plan (one cap) (one cap) (receipt cap).scope wrapper.summary tail :=
  .phiWithEarlier (scope := (receipt cap).scope) group (ready cap) (ready cap)
    (.finish (scope := afterGroup cap) wrapper (wrapperReady cap) (wrapperReady cap))

private def admitted (cap : Nat) :=
  Plan.analyzeNumberedAfterDelta numbered (receipt cap) (plan cap) (OmegaTerm.toTerm_toGraph source)

private def analysis (cap : Nat) := (admitted cap).get (by rfl)

private def requested : Demand := (· == 0)
private def emptyDemand : Demand := fun _ => false

#guard (analysis 3).linked.store == 27
#guard template.summaries.live (0 : Fin 1) emptyDemand == [.arg 0]
#guard template.summaries.live (0 : Fin 1) requested == [.arg 0, .arg 1]
#guard (analysis 3).liveCapture emptyDemand (.tail .head)
#guard (analysis 3).liveFormal requested .head
#guard !(analysis 3).liveFormal emptyDemand .head
#guard !(analysis 3).liveFormal requested (.tail .head)

example : Address.arg 2 ∈ ((analysis 3).problem requested).mayOut 0 :=
  ((analysis 3).mem_liveIn_iff requested _).1 (by decide)

private def args (spare : Nat) : Tuple machine.Val pair :=
  .cons (.data (41 : Nat)) (one spare)

private def run (fuel cap spare : Nat) :=
  Executable.run actions fuel 83 numbered (one cap) .head (args spare) 20

private def demand (want : Bool) : Demand := if want then requested else emptyDemand

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

private def blocked (observation : Except (Failure machine Nat) (Observation machine Nat single)) :
    Option (Nat × Nat × Nat × Nat) :=
  match observation with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, .cons (.global unitId vertex (.data n)) .nil⟩, _⟩ store) =>
    some (unitId, vertex, n, store)
  | _ => none

private def resumed (observation : Except (Failure machine Nat) (Observation machine Nat single)) :
    Option (Nat × Nat) :=
  match observation with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, _⟩, stack⟩ _) =>
    returned (observe actions (runFor actions 40 ⟨.returned .nil stack, 50⟩))
  | _ => none

#guard (run 40 3 4).toOption.bind returned == some (41, 43)
#guard (run 40 3 40).toOption.bind returned == some (41, 43)
#guard blocked (run 40 0 4) == some (83, 0, 0, 24)
#guard blocked (run 40 0 40) == some (83, 0, 0, 24)
#guard resumed (run 40 0 4) == some (41, 60)
#guard resumed (run 40 0 40) == some (41, 60)

-- Keep both first-step stores at 24 even when the initialized values differ.
private def first : DeltaTerm Op single [] (.data ()) :=
  ⟨single, .cons (.arg .head) .nil, [single], initializer false⟩

private def secondInitializer : RVSDG.Term Op [global] [] [single] single :=
  .bind ⟨[global], .simple .derive, .cons (.arg .head) .nil, fun i => i.elim0⟩
    (fun i => i.elim0) (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def second : DeltaTerm Op single past (.data ()) :=
  ⟨[global], .cons (.output (0 : Fin 2) .head) .nil, [single], secondInitializer⟩

private abbrev extendedPast := past ++ [[global]]
private abbrev context := [member.port, global, global]
private abbrev entry := context ++ exportFn.args

private def secondProbe : Code Op entry [single] [[], []] single true (some slots) :=
  .primitive .probe (.cons (.arg (.tail (.tail .head))) .nil)
    (.primitive .finish .nil (.ret (.cons (.output (0 : Fin 3) .head) .nil)))

private def downstream : Binding Op slots single extendedPast exportFn where
  context := context
  captures := .cons (.output (1 : Fin 3) .head)
    (.cons (.output (0 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil))
  sigs := [single, [], []]
  body := .familyCall (table := slots) memberSlot .head
    (.cons (.arg (.tail .head)) .nil) (.cons (.arg (.tail (.tail (.tail .head)))) .nil) secondProbe

private def last : ModuleTerm Op single extendedPast [[exportFn.port]] [exportFn.port] :=
  .bind (.lambda downstream.term) (.ret (lastExport extendedPast exportFn))

private def interleaved : OmegaTerm Op single [exportFn.port] [[global], [member.port], [global], [exportFn.port]] :=
  ⟨.bind (.delta first) (.bind (.phi group.term) (.bind (.delta second) last))⟩

private def start (capL capR : Nat) :=
  LinkedRemainder.start actions 83 interleaved.toGraph (one capL) (one capR) 20 (OmegaTerm.toTerm_toGraph interleaved)

private def beforeGroup (capL capR : Nat) :=
  (start capL capR).addDelta ⟨initialized capL, initialized capR, 24, rfl, rfl⟩

private def throughGroup (capL capR : Nat) :=
  (LinkedRemainder.addGroup (scope := (Scope.ordinary machine).addInitialized (initialized capL) (initialized capR))
    (binding := group) (beforeGroup capL capR) (ready capL) (ready capR)).get (by rfl)

private def atSecond (capL capR : Nat) := (throughGroup capL capR).checkDelta

#guard (atSecond 3 3).map (fun next =>
  match next.1.left with
  | .cons (.global unitId vertex (.data payload)) .nil =>
    let n : Nat := payload
    (unitId, vertex, n, next.2.store)) ==
    some (83, 2, 7, 35)
#guard (throughGroup 3 4).store == 24
#guard (atSecond 3 4).isNone

private def secondRow (cap : Nat) : Tuple machine.Val [global] :=
  .cons (.global 83 2 (.data (2 * cap + 1))) .nil

private def afterSecond (cap : Nat) := (afterGroup cap).addInitialized (secondRow cap) (secondRow cap)

private def advanced (cap : Nat) :=
  (throughGroup cap cap).addDelta ⟨secondRow cap, secondRow cap, 24 + 2 * cap + 5, rfl, rfl⟩

set_option maxHeartbeats 1000000 in
private theorem downstreamReady (cap : Nat) :
    downstream.resolved (afterSecond cap).guardL (one cap) (afterSecond cap).localsL :=
  fun _ _ => ⟨⟨rfl, rfl⟩, fun _ _ _ => trivial⟩

private def mixedAnalysis (cap : Nat) :=
  ((advanced cap).analyze
    (.finish (scope := afterSecond cap) downstream (downstreamReady cap) (downstreamReady cap))).get (by rfl)

#guard (mixedAnalysis 3).linked.store == 35
#guard (mixedAnalysis 3).liveCapture emptyDemand (.tail .head)
#guard (mixedAnalysis 3).liveCapture emptyDemand (.tail (.tail .head))
#guard (mixedAnalysis 3).liveFormal requested .head
#guard !(mixedAnalysis 3).liveFormal requested (.tail .head)

private def runMixed (fuel cap spare : Nat) :=
  Executable.run actions fuel 83 interleaved.toGraph (one cap) .head (args spare) 20

private def runMixedSubstituted (fuel cap : Nat) :=
  Executable.run actions fuel 83 interleaved.toGraph (one cap) .head
    ((mixedAnalysis cap).substituteDeadFormals requested (args 4) (args 40)) 20

example (fuel after cap : Nat) :
    ∃ left right, runMixed fuel cap 4 = .ok left ∧ runMixedSubstituted fuel cap = .ok right ∧
      PrefixObservationsAgree actions requested after left right :=
  (mixedAnalysis cap).linked_substituteDeadFormals requested fuel after (args 4) (args 40) (fun _ _ => rfl)

#guard (runMixed 60 3 4).toOption.bind returned == some (41, 58)
#guard (runMixedSubstituted 60 3).toOption.bind returned == some (41, 58)
#guard blocked (runMixed 60 0 4) == some (83, 0, 0, 29)
#guard blocked (runMixedSubstituted 60 0) == some (83, 0, 0, 29)
#guard resumed (runMixed 60 0 4) == some (41, 61)
#guard resumed (runMixedSubstituted 60 0) == some (41, 61)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.DeltaRegression
